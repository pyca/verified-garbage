variant!(o0, "../variants/o0.s");
variant!(o_diag8, "../variants/o_diag8.s");
variant!(u_noadox, "../variants/u_noadox.s");
variant!(u_noadd, "../variants/u_noadd.s");
fn variants() -> Vec<(&'static str, F)> { vec![("old rotate8", o0), ("diag 8-word groups", o_diag8), ("only redc no carry adox", u_noadox), ("only redc no add pass", u_noadd)] }
