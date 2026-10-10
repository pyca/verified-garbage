variant!(main_k, "../variants/main.s");
variant!(t_ossl, "../variants/t_ossl.s");
variant!(t_lite, "../variants/t_lite.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main", main_k), ("main with OpenSSL triangle (timing only)", t_ossl), ("main, triangle without base reloads", t_lite)] }
