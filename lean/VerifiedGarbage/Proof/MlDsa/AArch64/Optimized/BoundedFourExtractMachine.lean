import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourExtract

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

theorem vector_eq_of_bytes {x y : BitVec 128}
    (h : ∀i<16,vbyte x i=vbyte y i) : x=y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hh:=congrArg (fun b : BitVec 8=>b.getLsbD (k%8)) (h (k/8) (by omega))
  have h8 : k%8<8:=Nat.mod_lt _ (by decide)
  have hd : 8*(k/8)+k%8=k:=by omega
  simpa only [vbyte,BitVec.getLsbD_extractLsb',h8,decide_true,Bool.true_and,hd] using hh

theorem and_byteMask (x : BitVec 128) (m : BitVec 8) :
    x &&& (ofVBytes fun _=>m)=ofVBytes (fun i=>vbyte x i &&& m) := by
  apply vector_eq_of_bytes
  intro i hi
  rw [vbyte_ofVBytes _ hi]
  change (x &&& (ofVBytes fun _=>m)).extractLsb' (8*i) 8=_
  rw [BitVec.extractLsb'_and]
  exact congrArg (fun z=>vbyte x i &&& z) (vbyte_ofVBytes _ hi)

/-- Four low-to-high half-bytes are widened without observing later stream bytes. -/
theorem extract_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hm : s.v .v23=ofVBytes (fun _=>15)) (hi : s.v .v25=expandIndices)
    (k : ∀t,VChg [.v0,.v1] s t →
      (∀e<4,vword (t.v .v1) e=nibbleWord (s.v .v0) e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (([.vop (.logic .and .v1 .v0 .v23),
      .vop (.shift .ushr .b16 .v0 .v0 4),.vop (.perm .zip1 .b16 .v0 .v1 .v0),
      .vop (.tbl .v1 .v0 .v25)] : List Instr)++rest)) s Q := by
  refine wp_vop (d := .v1) rfl fun a ha => wp_vop (d := .v0) rfl fun b hb =>
    wp_vop (d := .v0) rfl fun c hc => wp_vop (d := .v1) rfl fun t ht => ?_
  refine k t ((((ha.chg.trans hb.chg).trans hc.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,hc.get .v25 (by decide),hb.get .v25 (by decide),ha.get .v25 (by decide),hi,
      hc.v,hb.get .v1 (by decide),ha.v,hm,and_byteMask,hb.v,ha.get .v0 (by decide)]
    exact extractVector_word _ he

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
