import VerifiedGarbage.Proof.RsaPss.AArch64.Select
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Compress

/-!
# RSASSA-PSS on AArch64: compressing every block

`compLoop` compresses each of the `nbm` blocks of `Y` into the hash value at
`scratch + oSt`, and copies it to `scratch + oSel` after block
`fb = ⌊(ℓ + L) / B⌋` (`compLoop_ok`): the hash value at `oSel` is then that
of the first `fb + 1` blocks.
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.MdStream.AArch64 (compressAt)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsl wp_add wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.AArch64 (CallOk compressAt_ok)
open VG.Proof.MdStream (Md)

/-- The `n` bytes of `Y` in the view `V`. -/
def yList (V : Nat → Byte) (n : Nat) : List Byte := (List.range n).map fun i => V (oY + i)

theorem yList_getD {V : Nat → Byte} {n i : Nat} (h : i < n) : (yList V n).getD i 0 = V (oY + i) := by
  simp [yList, List.getD_eq_getElem?_getD, h]

/-- The regions the compression loop writes: the compression function's
working space, the hash value and the selected hash value. -/
def CompW (so N o : Nat) : Prop := o < so ∨ (oSt ≤ o ∧ o < oSt + N) ∨ (oSel ≤ o ∧ o < oSel + N)

instance (so N o : Nat) : Decidable (CompW so N o) := by unfold CompW; infer_instance

section
variable {H : Hash} (hH : HashOK H)

/-- The compression loop, after the blocks before `b`. -/
structure CInv (t : State) (F S : Addr) (V₀ : Nat → Byte) (h₀ : hH.md.HV) (nbm fb : Nat) (b : Nat)
    (u : State) : Prop where
  sp : u.sp = t.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28], u.gpr r = t.gpr r
  x27 : u.gpr .x27 = BitVec.ofNat 64 b
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  fr : Frame [⟨S, oRsa⟩] t.mem u.mem
  keep : ∀ o < oRsa, ¬ CompW H.P.so H.P.N o → u.mem (off S o) = V₀ o
  st : hH.md.stateAt u.mem (off S oSt) = hH.md.compressList h₀ (yList V₀ (nbm * H.P.B)) b
  sel : fb < b → hH.md.stateAt u.mem (off S oSel) = hH.md.compressList h₀ (yList V₀ (nbm * H.P.B)) (fb + 1)

/-- An address of the working space outside a region of it. -/
theorem not_in (S : Addr) {o e k : Nat} (h : o + 1 ≤ e ∨ e + k ≤ o) (ho : o < 8192) (he : e + k ≤ 8192) :
    ¬ (⟨off S e, k⟩ : Region).Contains (off S o) 1 :=
  fun hc => Offset.disjoint S h (by omega) (by omega) _ (Region.contains_self _ _) hc

theorem not_in0 (S : Addr) {o k : Nat} (h : k ≤ o) (ho : o < 8192) (hk : k ≤ 8192) :
    ¬ (⟨S, k⟩ : Region).Contains (off S o) 1 := by
  have := not_in S (o := o) (e := 0) (k := k) (.inr (by omega)) ho (by omega)
  rwa [off, BitVec.add_zero] at this

theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

include hH in
theorem so_lt : H.P.so < 2048 := by
  have := hH.sizes.fits; have := hH.W; omega

theorem lsl_val {x k : Nat} (hx : x * 2 ^ k < 2 ^ 64) : BitVec.ofNat 64 x <<< k = BitVec.ofNat 64 (x * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hx),
    Nat.mod_eq_of_lt hx]

/-- One block. -/
theorem comp_step {t : State} {F S : Addr} (L : Lay t F S) {V₀ : Nat → Byte} {h₀ : hH.md.HV} {ℓ nbm b : Nat}
    (hB : 2 ^ lgB H = H.P.B) (hlg : lgB H < 64) (hℓ : ℓ < 2 ^ 62) (hnb : nbm * H.P.B ≤ 2048) (hb : b < nbm)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 ℓ) (h19 : t.gpr .x19 = off S oSt)
    (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm) {u : State}
    (I : CInv hH t F S V₀ h₀ nbm ((ℓ + H.P.L) / H.P.B) b u) :
    WP isa (seqs [.block (compArgs H), compressAt H.compN H.compC, select H, .block nextBlock]) u fun u' =>
      CInv hH t F S V₀ h₀ nbm ((ℓ + H.P.L) / H.P.B) (b + 1) u' ∧
        ((u'.gpr .x9).toNat ≠ 0 ↔ b + 1 ≠ nbm) := by
  generalize hfbd : (ℓ + H.P.L) / H.P.B = fb at I ⊢
  have hso := so_lt hH
  have hN := hH.N_le
  have hN0 := hH.sizes.dims.N.1
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.L
  have hBb : H.P.B * (b + 1) ≤ H.P.B * nbm := Nat.mul_le_mul_left _ hb
  have hBn : H.P.B * nbm ≤ 2048 := by rw [Nat.mul_comm]; exact hnb
  have hBb' : H.P.B * b + H.P.B ≤ H.P.B * nbm := by rw [← Nat.mul_succ]; exact hBb
  have hcm : b * H.P.B = H.P.B * b := Nat.mul_comm _ _
  have hnb1 : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right _ hB0) hnb
  have Lu : Lay u F S := L.congr I.sp I.wr (by rw [I.cs .x20 (by decide)])
  simp only [seqs]
  unfold compArgs
  refine WP.seq (wp_lsl hlg fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_addImm (by decide) fun u₃ o₃ e₃ => wp_nil ?_)
  have O₃ : Only [.x1] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  have x1 : u₃.gpr .x1 = off S (oY + H.P.B * b) := by
    rw [e₃, e₂, e₁, o₁.get .x20, I.x27, I.cs .x20 (by decide), L.x20, lsl_val (by rw [hB]; omega),
      hB]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mul_comm b]; omega
  have hcall : CallOk u₃ H.P.N H.P.B H.P.so (off S oSt) S (off S (oY + H.P.B * b)) := {
    x19 := by rw [O₃.get .x19, I.cs .x19 (by decide), h19]
    x20 := by rw [O₃.get .x20, I.cs .x20 (by decide), L.x20]
    x1 := x1
    st_scr := by
      have := Offset.disjoint S (d := oSt) (n := H.P.N) (e := 0) (k := H.P.so) (by unfold oSt; omega)
        (by unfold oSt; omega) (by omega)
      rwa [BitVec.add_zero] at this
    src_st := Offset.disjoint S (by unfold oY oSt; omega) (by unfold oY; omega) (by unfold oSt; omega)
    src_scr := by
      have := Offset.disjoint S (d := oY + H.P.B * b) (n := H.P.B) (e := 0) (k := H.P.so) (by unfold oY; omega)
        (by unfold oY; omega) (by omega)
      rwa [BitVec.add_zero] at this
    cov := by
      rw [O₃.rd, O₃.wr]
      refine Covers.cons (Covers.one (Lu.ld (by unfold oY oRsa; omega))) (Covers.cons
        (Covers.one (Lu.ld (by unfold oSt oRsa; omega))) (Covers.cons (Covers.one ?_) Covers.nil))
      have := Lu.ld (o := 0) (n := H.P.so) (by unfold oRsa; omega)
      rwa [off, BitVec.add_zero] at this
    covW := by
      rw [O₃.wr]
      refine Covers.cons (Covers.one (Lu.st (by unfold oSt oRsa; omega))) (Covers.cons (Covers.one ?_) Covers.nil)
      have := Lu.st (o := 0) (n := H.P.so) (by unfold oRsa; omega)
      rwa [off, BitVec.add_zero] at this }
  refine WP.seq (WP.mono (WP.preservedV (compressAt_ok hH.comp hcall (Q := fun s' => s'.rd = u₃.rd ∧
      s'.wr = u₃.wr ∧ (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = u₃.gpr r) ∧ s'.sp = u₃.sp ∧
      Frame [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩] u₃.mem s'.mem ∧
      hH.md.stateAt s'.mem (off S oSt) = hH.md.compress (hH.md.stateAt u₃.mem (off S oSt))
        (hH.md.blockAt u₃.mem (off S (oY + H.P.B * b))))
      fun s' a b c d e f => ⟨a, b, c, d, e, f⟩) (by rw [Code.allInstrs_eq]; exact hH.cmp_keepsV))
    fun v ⟨⟨vrd, vwr, vcs, vsp, vfr, vst⟩, vv⟩ => ?_)
  have Lv : Lay v F S := Lu.congr (by rw [vsp, O₃.sp]) (by rw [vwr, O₃.wr])
    (by rw [vcs .x20 (by decide) (by decide), O₃.get .x20])
  have v22 : v.gpr .x22 = BitVec.ofNat 64 ℓ := by
    rw [vcs .x22 (by decide) (by decide), O₃.get .x22, I.cs .x22 (by decide), h22]
  have v27 : v.gpr .x27 = BitVec.ofNat 64 b := by rw [vcs .x27 (by decide) (by decide), O₃.get .x27, I.x27]
  refine WP.seq (WP.mono (select_ok H Lv (V := fun o => v.mem (off S o)) (fun _ _ => rfl) hB hlg hN0 hN hL.2 hℓ
    (by omega) v22 v27) fun w ⟨wK, wfr, wR⟩ => ?_)
  rw [hfbd] at wR
  -- the frame's slot is kept
  have frS : Frame [⟨S, oRsa⟩] t.mem w.mem := by
    refine I.fr.trans ((Frame.sub (by rw [O₃.mem] at vfr; exact vfr) fun r hr => ?_).trans wfr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by unfold oSt oRsa; omega)⟩
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold oRsa; omega)⟩
  have slot : w.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by
    rw [frS.readW (r := ⟨F, frameBytes⟩) (Offset.contains_base _ (by decide) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact L.dFS) (by decide), hNb]
  refine wp_addImm (by decide) fun w₁ p₁ f₁ => wp_ldrSp (by decide) ?_ fun w₂ p₂ f₂ =>
    wp_sub fun w₃ p₃ f₃ => wp_nil ?_
  · rw [p₁.sp, wK.sp, Lv.sp, p₁.rd, p₁.wr, wK.rd, wK.wr]; exact Lv.fld (d := sNb) (n := 8) (by decide)
  have P₃ : Only [.x27, .x9] w w₃ := (p₁.trans (p₂.trans p₃)).mono
  rw [p₁.sp, wK.sp, Lv.sp, p₁.mem, slot] at f₂
  have x27 : w₃.gpr .x27 = BitVec.ofNat 64 (b + 1) := by
    rw [p₃.get .x27, p₂.get .x27, f₁, wK.get .x27, v27, BitVec.ofNat_add_ofNat]
  -- bytes outside the regions the call and the selection write
  have wv : ∀ o < oRsa, ¬ (oSel ≤ o ∧ o < oSel + H.P.N) → w.mem (off S o) = v.mem (off S o) := fun o ho h => by
    rw [wR o ho]; simp only [vSel]; rw [ite_eq_right (fun h' => h h'.2)]
  have vu : ∀ o < oRsa, ¬ (oSt ≤ o ∧ o < oSt + H.P.N) → H.P.so ≤ o → v.mem (off S o) = u.mem (off S o) :=
    fun o ho h h' => by
      rw [vfr (off S o) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact not_in S (by omega) (by unfold oRsa at ho; omega) (by unfold oSt; omega)
        · exact not_in0 S h' (by unfold oRsa at ho; omega) (by omega)), O₃.mem]
  have hY : ∀ k < H.P.B, u.mem (off S (oY + H.P.B * b) + BitVec.ofNat 64 k) =
      (yList V₀ (nbm * H.P.B)).getD (H.P.B * b + k) 0 := fun k hk => by
    rw [off_add, yList_getD (by rw [Nat.mul_comm nbm]; omega), I.keep _ (by unfold oY oRsa; omega)
      (by unfold CompW oY oSt oSel; omega), Nat.add_assoc]
  have stw : hH.md.stateAt w.mem (off S oSt) = hH.md.compressList h₀ (yList V₀ (nbm * H.P.B)) (b + 1) := by
    rw [hH.md.stateAt_congr (mem := v.mem) fun i hi => by
        rw [off_add]; exact wv _ (by unfold oSt oRsa; omega) (by unfold oSt oSel; omega), vst,
      O₃.mem, I.st, hH.md.compressList_succ]
    exact congrArg _ (hH.md.parse_congr fun k hk => hY k hk)
  refine ⟨⟨?sp, ?rd, ?wr, ?cs, x27, ?vec, ?fr, ?keep, ?st, ?sel⟩, ?flag⟩
  case sp => rw [P₃.sp, wK.sp, vsp, O₃.sp, I.sp]
  case rd => rw [P₃.rd, wK.rd, vrd, O₃.rd, I.rd]
  case wr => rw [P₃.wr, wK.wr, vwr, O₃.wr, I.wr]
  case cs =>
    intro r hr
    have h1 : r ∉ [Reg.x27, .x9] := by revert r; decide
    have h2 : r ∉ [Reg.x15, .x9, .x13, .x10, .x11, .x12, .x14] := by revert r; decide
    have h3 : r ∈ preserved := by revert r; decide
    have h4 : r ≠ .x30 := by revert r; decide
    have h5 : r ∉ [Reg.x1] := by revert r; decide
    rw [P₃.gpr r h1, wK.gpr r h2, vcs r h3 h4, O₃.gpr r h5, I.cs r hr]
  case vec => intro r hr; rw [P₃.vcs r hr, wK.vcs r hr, vv r hr, O₃.vcs r hr, I.vec r hr]
  case fr => rw [P₃.mem]; exact frS
  case keep =>
    intro o ho h
    unfold CompW at h
    rw [P₃.mem, wv o ho (by omega), vu o ho (by omega) (by omega), I.keep o ho (by unfold CompW; omega)]
  case st => rw [P₃.mem]; exact stw
  case sel =>
    intro hfb
    rw [P₃.mem]
    by_cases e : b = fb
    · rw [hH.reloc w.mem w.mem (off S oSt) (off S oSel) fun i hi => by
        rw [off_add, off_add, wR _ (by unfold oSel oRsa; omega)]; simp only [vSel]
        rw [ite_eq_left ⟨e, by omega, by omega⟩, Nat.add_sub_cancel_left]
        exact (wv _ (by unfold oSt oRsa; omega) (by unfold oSt oSel; omega)).symm, stw, e]
    · rw [hH.md.stateAt_congr (mem := u.mem) fun i hi => by
        rw [off_add, wR _ (by unfold oSel oRsa; omega)]; simp only [vSel]
        rw [ite_eq_right (fun h' => e h'.1)]
        exact vu _ (by unfold oSel oRsa; omega) (by unfold oSel oSt; omega) (by unfold oSel; omega)]
      exact I.sel (by omega)
  case flag =>
    rw [f₃, f₂, p₂.get .x27, f₁, wK.get .x27, v27, BitVec.ofNat_add_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega

end

end VG.Proof.RsaPss.AArch64
