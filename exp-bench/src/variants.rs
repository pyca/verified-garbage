variant!(xs_cur, "../variants/xs_cur.s");
variant!(xs_tri, "../variants/xs_tri.s");
variant!(xs_ssesel, "../variants/xs_ssesel.s");
fn variants() -> Vec<(&'static str, F)> { vec![("main + xmm6/7", xs_cur), ("triangle rows without xor/first adox", xs_tri), ("select by SSE masks", xs_ssesel)] }
