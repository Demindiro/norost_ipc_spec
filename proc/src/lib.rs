#![feature(proc_macro_expand)]

extern crate proc_macro;
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use std::{cell::Cell, collections::BTreeMap, mem};

macro_rules! error {
    ($($arg:tt)+) => {{
        let s = format!($($arg)+);
        TokenStream::from(quote! { compile_error!(#s); })
    }};
}

trait MemberMap<'a> {
    fn add(&mut self, name: &'a str, ty: Type<'a>) -> Result<(), TokenStream>;

    fn get(&self, name: &'a str) -> Result<&Type<'a>, TokenStream>;

    fn iter(&self) -> Box<dyn Iterator<Item = (&'a str, &Type<'a>)> + '_>;
}

impl<'a> MemberMap<'a> for Vec<(&'a str, Type<'a>)> {
    fn add(&mut self, name: &'a str, ty: Type<'a>) -> Result<(), TokenStream> {
        if <[_]>::iter(self).any(|(n, _)| *n == name) {
            Err(error!("field {:?} already exists", name))
        } else {
            self.push((name, ty));
            Ok(())
        }
    }

    fn get(&self, name: &'a str) -> Result<&Type<'a>, TokenStream> {
        if let Some((_, ty)) = Vec::iter(self).find(|(n, _)| *n == name) {
            Ok(ty)
        } else {
            Err(error!("field {:?} not found", name))
        }
    }

    fn iter(&self) -> Box<dyn Iterator<Item = (&'a str, &Type<'a>)> + '_> {
        Box::new(<[_]>::iter(self).map(|(k, v)| (*k, v)))
    }
}

type TypeMap<'a, M> = BTreeMap<&'a str, UserType<'a, M>>;

#[proc_macro]
pub fn make_answer(item: TokenStream) -> TokenStream {
    let mut it = item.expand_expr().unwrap().into_iter();
    let s = it.next().unwrap();
    assert!(it.next().is_none());
    match litrs::Literal::try_from(s) {
        Err(e) => e.to_compile_error(),
        Ok(litrs::Literal::String(s)) => parse_spec(s.value()).map_or_else(|v| v, |v| v),
        Ok(_) => error!("expected string"),
    }
}

fn parse_spec(s: &str) -> Result<TokenStream, TokenStream> {
    let mut tokens = SplitWithSeparators(s).map(|w| {
        Ok(match w {
            ":" => Token::DoubleColon,
            "{" => Token::CurlyOpen,
            "}" => Token::CurlyClose,
            "struct" => Token::Struct,
            "union" => Token::Union,
            "enum" => Token::Enum,
            "alias" => Token::Alias,
            "@name" => Token::MetaName,
            "@version" => Token::MetaVersion,
            "@abi" => Token::MetaAbi,
            "type" | "try" | "catch" | "class" => Err(error!("{:?} is a reserved keyword", w))?,
            w if w.starts_with('@') => return Err(error!("unknown attribute {:?}", w)),
            w if b"us".contains(&w.as_bytes()[0])
                && w.bytes().skip(1).all(|c| c.is_ascii_digit()) =>
            {
                let bits = w[1..].parse().unwrap();
                if w.as_bytes()[0] == b'u' {
                    Token::Unsigned { bits }
                } else {
                    Token::Signed { bits }
                }
            }
            w if w.bytes().all(|c| c.is_ascii_digit()) => Token::Num(w.parse().unwrap()),
            w if w
                .bytes()
                .all(|c| c.is_ascii_alphanumeric() | b"._".contains(&c)) =>
            {
                Token::Ident(w)
            }
            w => todo!("parse {:?}", w),
        })
    });

    let mut types = TypeMap::new();
    let mut name = None;
    let mut version = None;
    let mut abi = None;

    let parse_ty = |t| match t {
        Token::Ident(n) => Some(Type::Ident(n)),
        Token::Unsigned { bits } => Some(Type::Unsigned { bits }),
        Token::Signed { bits } => Some(Type::Signed { bits }),
        _ => None,
    };

    while let Some(t) = tokens.next() {
        let mut next = || {
            tokens
                .next()
                .ok_or_else(|| error!("unexpected end of token stream"))
        };
        let t = t?;
        match t {
            Token::MetaName => {
                assert!(name.is_none());
                name = Some(next()??.as_ident().unwrap());
            }
            Token::MetaVersion => {
                assert!(version.is_none());
                version = Some(next()??.as_num().unwrap());
            }
            Token::MetaAbi => {
                assert!(abi.is_none());
                abi = Some(next()??.as_num().unwrap());
            }
            Token::Alias => {
                let l = next()??.as_ident().unwrap();
                assert!(!types.contains_key(l));
                assert_eq!(next()??, Token::DoubleColon);
                let v = parse_ty(next()??).unwrap();
                types.insert(l, UserType::new(CustomType::Alias(v)));
            }
            Token::Struct | Token::Union => {
                let l = next()??.as_ident().unwrap();
                assert!(!types.contains_key(l));
                assert_eq!(next()??, Token::CurlyOpen);
                let mut members = Vec::default();
                loop {
                    let t = next()??;
                    if t == Token::CurlyClose {
                        break;
                    }
                    let m = t.as_ident().unwrap();
                    assert_eq!(next()??, Token::DoubleColon);
                    members.add(m, parse_ty(next()??).unwrap())?;
                }
                let v = if t == Token::Struct {
                    CustomType::Struct(members)
                } else {
                    CustomType::Union(members)
                };
                types.insert(l, UserType::new(v));
            }
            Token::Enum => {
                let l = next()??.as_ident().unwrap();
                assert!(!types.contains_key(l));
                assert_eq!(next()??, Token::CurlyOpen);
                let mut variants = Vec::default();
                loop {
                    let t = next()??;
                    if t == Token::CurlyClose {
                        break;
                    }
                    let m = t.as_ident().unwrap();
                    assert!(!variants.contains(&m));
                    variants.push(m);
                }
                types.insert(l, UserType::new(CustomType::Enum(variants)));
            }
            t => return Err(error!("unexpected token {:?}", t)),
        }
    }

    generate_rust(types)
}

fn generate_rust<'a>(
    types: TypeMap<'a, Vec<(&'a str, Type<'a>)>>,
) -> Result<TokenStream, TokenStream> {
    let mut stream = TokenStream::new();
    let mut e = |q| stream.extend(TokenStream::from(q));
    for (name, t) in &types {
        let name = format_ident!("{}", name);
        match &t.1 {
            CustomType::Alias(v) => {
                let ty = v.to_tokens();
                e(quote! { type #name = #ty; });
            }
            CustomType::Enum(v) => {
                let mut vars = quote! {};
                let mut to_raw = quote! {};
                let mut from_raw = quote! {};
                for (i, v) in v.iter().enumerate() {
                    let v = format_ident!("{}", v);
                    vars.extend(quote! { #v, });
                    to_raw.extend(quote! { Self::#v => #i, });
                    from_raw.extend(quote! { #i => Self::#v, });
                }
                let raw = Type::Unsigned {
                    bits: t.calc_size(&types),
                }
                .to_tokens();
                e(quote! {
                    pub enum #name { #vars }

                    impl #name {
                        #[inline(always)]
                        pub fn from_raw(slice: &[u8], offset: usize) -> Option<Self> {
                            Some(match usize::try_from(<#raw>::from_raw(slice, offset).get()).unwrap() {
                                #from_raw
                                _ => return None
                            })
                        }

                        #[inline(always)]
                        pub fn to_raw(&self, slice: &mut [u8], offset: usize) {
                            <#raw>::new(match self {
                                #to_raw
                            }.try_into().unwrap()).to_raw(slice, offset)
                        }
                    }
                });
            }
            CustomType::Struct(m) => {
                let size = t.calc_size(&types);
                let size = size + 7 >> 3; // min amount of bytes necessary
                let size = usize::try_from(size).unwrap();
                let mut methods = quote! {};
                let mut offset = 0;
                for (name, ty) in m {
                    let get_f = format_ident!("{}", name);
                    let set_f = format_ident!("set_{}", name);
                    let s = ty.calc_size(&types);
                    let non_exhaustive = ty.has_undef_patterns(&types);
                    let ty = ty.to_tokens();
                    methods.extend(if non_exhaustive {
                        quote! {
                            pub fn #get_f(&self) -> Option<#ty> {
                                <#ty>::from_raw(&self.0, #offset)
                            }
                        }
                    } else {
                        quote! {
                            pub fn #get_f(&self) -> #ty {
                                <#ty>::from_raw(&self.0, #offset)
                            }
                        }
                    });
                    methods.extend(quote! {
                        pub fn #set_f(&mut self, value: #ty) {
                            value.to_raw(&mut self.0, #offset)
                        }
                    });
                    offset += s as usize;
                }
                e(quote! {
                    pub struct #name([u8; #size]);

                    impl #name {
                        #methods

                        #[inline(always)]
                        pub fn from_raw(slice: &[u8], offset: usize) -> Self {
                            if offset % 8 == 0 {
                                Self(slice[offset / 8..][..#size].try_into().unwrap())
                            } else {
                                todo!("non-byte-aligned offset")
                            }
                        }

                        #[inline(always)]
                        pub fn to_raw(&self, slice: &mut [u8], offset: usize) {
                            if offset % 8 == 0 {
                                slice[offset / 8..][..#size].copy_from_slice(&self.0)
                            } else {
                                todo!("non-byte-aligned offset")
                            }
                        }
                    }

                    impl Default for #name {
                        fn default() -> Self {
                            Self([0; #size])
                        }
                    }
                });
            }
            CustomType::Union(m) => {
                let size = t.calc_size(&types);
                let size = size + 7 >> 3; // min amount of bytes necessary
                let size = usize::try_from(size).unwrap();
                let mut methods = quote! {};
                for (name, ty) in m {
                    let get_f = format_ident!("{}", name);
                    let set_f = format_ident!("set_{}", name);
                    //let s = ty.calc_size(&types);
                    let ty = ty.to_tokens();
                    methods.extend(quote! {
                        pub fn #get_f(&self) -> #ty {
                            <#ty>::from_raw(&self.0, 0)
                        }

                        #[inline(always)]
                        pub fn #set_f(&mut self, value: #ty) {
                            value.to_raw(&mut self.0, 0)
                        }
                    });
                }
                e(quote! {
                    pub struct #name([u8; #size]);

                    impl #name {
                        #methods

                        #[inline(always)]
                        pub fn from_raw(slice: &[u8], offset: usize) -> Self {
                            if offset % 8 == 0 {
                                Self(slice[offset / 8..][..#size].try_into().unwrap())
                            } else {
                                todo!("non-byte-aligned offset")
                            }
                        }

                        #[inline(always)]
                        pub fn to_raw(&self, slice: &mut [u8], offset: usize) {
                            if offset % 8 == 0 {
                                slice[offset / 8..][..#size].copy_from_slice(&self.0)
                            } else {
                                todo!("non-byte-aligned offset")
                            }
                        }
                    }

                    impl Default for #name {
                        fn default() -> Self {
                            Self([0; #size])
                        }
                    }
                });
            }
        };
    }
    Ok(stream)
}

fn gen_signed_type(bits: u32) -> quote::__private::TokenStream {
    let name = format_ident!("S{}", bits);
    quote! { ::norost_ipc_spec::#name }
}

fn gen_unsigned_type(bits: u32) -> quote::__private::TokenStream {
    let name = format_ident!("U{}", bits);
    quote! { ::norost_ipc_spec::#name }
}

struct SplitWithSeparators<'a>(&'a str);

impl<'a> Iterator for SplitWithSeparators<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        let mut it = self.0.bytes().enumerate();
        while let Some((start, c)) = it.next() {
            let s;
            match c {
                b' ' | b'\t' | b'\n' => {}
                b'{' | b'}' | b':' => {
                    (s, self.0) = self.0.split_at(start + 1);
                    return Some(&s[start..]);
                }
                _ => {
                    while let Some((i, d)) = it.next() {
                        if b" \t\n{}:".contains(&d) {
                            (s, self.0) = self.0.split_at(i);
                            return Some(&s[start..]);
                        }
                    }
                    return Some(mem::take(&mut self.0));
                }
            }
        }
        None
    }
}

#[derive(Debug, PartialEq)]
enum Token<'a> {
    Ident(&'a str),
    Unsigned { bits: u32 },
    Signed { bits: u32 },
    Num(isize),
    Union,
    Struct,
    Enum,
    Alias,
    DoubleColon,
    CurlyOpen,
    CurlyClose,
    MetaName,
    MetaVersion,
    MetaAbi,
}

impl<'a> Token<'a> {
    fn as_ident(&self) -> Option<&'a str> {
        match self {
            Self::Ident(s) => Some(*s),
            _ => None,
        }
    }

    fn as_num(&self) -> Option<isize> {
        match self {
            Self::Num(s) => Some(*s),
            _ => None,
        }
    }
}

#[derive(Debug)]
struct UserType<'a, M: MemberMap<'a>>(Cell<TypeState>, CustomType<'a, M>);

impl<'a, M: MemberMap<'a>> UserType<'a, M> {
    fn new(ty: CustomType<'a, M>) -> Self {
        Self(Cell::new(TypeState::Unresolved), ty)
    }

    fn calc_size(&self, types: &TypeMap<'a, M>) -> u32 {
        match self.0.get() {
            TypeState::Resolved(n) => n,
            TypeState::Resolving => panic!("recursive type"),
            TypeState::Unresolved => {
                self.0.set(TypeState::Resolving);
                let n = self.1.calc_size(types);
                self.0.set(TypeState::Resolved(n));
                n
            }
        }
    }

    fn has_undef_patterns(&self, types: &TypeMap<'a, M>) -> bool {
        self.1.has_undef_patterns(types)
    }
}

#[derive(Debug)]
enum CustomType<'a, M: MemberMap<'a>> {
    Struct(M),
    Union(M),
    Enum(Vec<&'a str>),
    Alias(Type<'a>),
}

impl<'a, M: MemberMap<'a>> CustomType<'a, M> {
    fn calc_size(&self, types: &TypeMap<'a, M>) -> u32 {
        match self {
            Self::Struct(m) => m.iter().map(|(_, t)| t.calc_size(types)).sum(),
            Self::Union(m) => m.iter().map(|(_, t)| t.calc_size(types)).max().unwrap_or(0),
            Self::Enum(v) => ceil_log2(v.len()).try_into().unwrap(),
            Self::Alias(t) => t.calc_size(types),
        }
    }

    fn has_undef_patterns(&self, types: &TypeMap<'a, M>) -> bool {
        match self {
            Self::Enum(v) => !v.is_empty() && v.len().count_ones() != 1,
            Self::Struct(_) | Self::Union(_) => false,
            Self::Alias(t) => t.has_undef_patterns(types),
        }
    }
}

fn ceil_log2(n: usize) -> u32 {
    n.checked_sub(1)
        .map_or(0, |n| mem::size_of_val(&n) as u32 * 8 - n.leading_zeros())
}

#[derive(Debug)]
enum Type<'a> {
    Ident(&'a str),
    Unsigned { bits: u32 },
    Signed { bits: u32 },
}

impl<'a> Type<'a> {
    fn calc_size<M: MemberMap<'a>>(&self, types: &TypeMap<'a, M>) -> u32 {
        match self {
            Self::Ident(n) => types[n].calc_size(types),
            Self::Signed { bits } | Self::Unsigned { bits } => *bits,
        }
    }

    fn to_tokens(&self) -> quote::__private::TokenStream {
        match self {
            Type::Ident(n) => {
                let n = format_ident!("{}", n);
                quote! { #n }
            }
            Type::Signed { bits } => gen_signed_type(*bits),
            Type::Unsigned { bits } => gen_unsigned_type(*bits),
        }
    }

    fn has_undef_patterns<M: MemberMap<'a>>(&self, types: &TypeMap<'a, M>) -> bool {
        match self {
            Self::Ident(n) => types[n].has_undef_patterns(types),
            Self::Signed { .. } | Self::Unsigned { .. } => false,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum TypeState {
    Unresolved,
    Resolving,
    Resolved(u32),
}
