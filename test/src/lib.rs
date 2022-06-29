norost_ipc_spec::compile!(include_str!("../spec/stream_table.ipc"));

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn convert_request_type() {
		use RequestType::*;
		for t in [Read, Write, Open, Close, Create, Destroy] {
			let mut a @ mut b = [0];
			t.to_raw(&mut a, 0);
			RequestType::from_raw(&a, 0).unwrap().to_raw(&mut b, 0);
			assert_eq!(a, b);
		}
	}

	#[test]
	fn convert_request() {
		let mut a @ mut b = [0];
		let mut v = Request::default();
		RequestType::Share.to_raw(&mut a, 0);
		v.set_ty(RequestType::Share);
		v.ty().unwrap().to_raw(&mut b, 0);
		assert_eq!(a, b);
	}
}
