import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Layout

/-!
# Ed448 verification on AArch64: the frame's body

From the saved arguments (`Args`) and `scratch` in `x6`: the entry keeps
`scratch` and the header of `dom4` in the locals (`entry_ok`), the hash
`H(dom4(0, C) ‖ R ‖ A ‖ M)` is squeezed into the locals (`hash_ok`), reduced
into `k` (`reduce_step`), and `x0` is the verification equation's result
(`body_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS keep hdr)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue readW_eq_read)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The saved arguments, and the comb's words. -/
def Args (L : Lay) (m : Mem) : Prop :=
  (∀ j < 6, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.arg j) ∧
    VG.Proof.Ed448.AArch64.Whole.TblWords L.T m

abbrev Ctx0 (L : Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx L.E g vec m₀ L.env.ins L.env.outs t

theorem args_sub (L : Lay) : Region.Sub (ARGS L.E) L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

/-- What the body may write misses the saved arguments. -/
theorem args_apart (hL : L.Ok) : ∀ r ∈ L.env.outs ++ [FR L.E, CK L.E], (ARGS L.E).Disjoint r := by
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.kc.sub_left (args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)
  · exact ((Offset.below_disjoint L.E (m := 16) (l := 304) (by decide)).sub_right
      (Offset.sub_base _ (by decide : 256 + 48 ≤ 304))).symm

theorem arg_word (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) {j : Nat} (hj : j < 6) :
    t.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * j)) 8 = L.arg j := by
  rw [← readW_eq_read, ← ha.1 j hj]
  exact hc.frame.readW (r := ARGS L.E) (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega)
    (by decide)) (args_apart hL) (by decide)

theorem arg_src (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) {j : Nat} (hj : j < 6)
    (x0 : BitVec 64) : srcValue L.E t.mem x0 (.val (.caller j 0)) = L.arg j := by
  simp only [srcValue, VG.Proof.Ed25519.AArch64.Whole.value]
  rw [arg_word hL hc ha hj, BitVec.add_zero]

/-- An input's bytes, as on entry. -/
theorem in_bytes (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) {R : Region} (hR : R ∈ L.inputs)
    {n : Nat} (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt t.mem R.base n = Spec.Sha3.bytesAt m₀ R.base n := by
  unfold Spec.Sha3.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := R) ?_ hl (by
    have := List.mem_range.mp hi; omega)
  simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hR
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> rcases hR with rfl | rfl | rfl | rfl | rfl
  exacts [hL.pc, hL.cc, hL.mc, hL.sc, hL.tbc, (hL.kp.sub_left (frame_sub L)).symm,
    (hL.kx.sub_left (frame_sub L)).symm, (hL.km.sub_left (frame_sub L)).symm,
    (hL.ks.sub_left (frame_sub L)).symm, hL.tbk.sub_right (frame_sub L), hL.cp.symm, hL.cx.symm,
    hL.cm.symm, hL.cs.symm, hL.tbck]

/-- `scratch` kept, and the header of `dom4`. -/
theorem entry_ok (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.scr)
    (hsy : t.syms Impl.X448.AArch64.Base.combSym = L.T) :
    WP isa (.block entry) t fun u => WCtx L.env g vec m₀ u := by
  have hfr : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  rw [entry, WP.block_append_iff]
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.Whole.keep_ok (r := .x6) (d := fScr) (by decide)
    ⟨_, hfr, Offset.contains_base _ (by decide) (by decide)⟩) fun a ⟨ka, _, am⟩ sa => ?_
  have hfa : (⟨a.sp, 256⟩ : Region) ∈ a.wr := by rw [ka.sp, ka.wr]; exact hfr
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.Whole.hdr_ok (d := fHdr) (j := 2) (by decide) (by decide) hfa (by
    rw [ka.rd, ka.wr, ka.sp, hc.rd, hc.wr, hc.sp]
    exact ⟨ARGS L.E, List.mem_append_left _ (by simp [Lay.env]),
      Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)⟩)) fun u ⟨ku, um⟩ su => ?_
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x15), h6, hc.sp] at am
  rw [ka.sp, hc.sp] at um
  have hread : a.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * 2)) 8 = L.ctxLen := by
    rw [am, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide))]
    exact arg_word hL hc ha (j := 2) (by decide)
  rw [hread] at um
  have hf : Frame [FR L.E] t.mem u.mem := by
    rw [um, am]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_ |>.writeW (List.mem_singleton_self _) _ ?_)
      |>.writeW (List.mem_singleton_self _) _ ?_
    · exact Offset.contains_base _ (by decide) (by decide)
    · exact Offset.contains_base _ (by decide) (by decide)
    · exact Offset.contains_base _ (by decide) (by decide)
  refine ⟨hc.of_frame (ku.rd.trans ka.rd) (ku.wr.trans ka.wr) (ku.sp.trans ka.sp) (fun r hr _ => ?_)
    (fun r _ => by rw [ku.v, ka.v]) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl fun _ h => h),
    ?_, by rw [su, sa]; exact hsy⟩
  · rw [ku.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr),
      ka.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)]
  · intro p hp
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · show u.mem.read (L.E + BitVec.ofNat 64 fScr) 8 = L.scr
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
        VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)), am,
        VG.Proof.Ed448.AArch64.Whole.read_writeW_self]
    · show u.mem.read (L.E + BitVec.ofNat 64 fHdr) 8 = sigWord
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
        VG.Proof.Ed448.AArch64.Whole.read_writeW_self]
    · show u.mem.read (L.E + BitVec.ofNat 64 (fHdr + 8)) 8 = L.ctxLen <<< 8
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_self]

end VG.Proof.Ed448.AArch64.Verify
