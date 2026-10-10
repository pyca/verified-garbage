variant!(main_k, "../variants/main.s");
variant!(lite_k, "../variants/lite.s");
variant!(stream_k, "../variants/stream.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main", main_k), ("triangle base in rcx (PR)", lite_k), ("+ tiles stream the columns", stream_k)] }
