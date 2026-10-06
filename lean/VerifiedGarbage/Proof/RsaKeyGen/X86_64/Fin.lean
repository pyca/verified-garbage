import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Entry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Store

/-!
# A candidate on x86-64: zeros to `out`, and the ends

`zeroOut_ok`: zeros to the `out_len` octets of `out`; `finish_ok`: `rax` to
`used`, the status returned and the saved registers restored, for `finNone`,
`finUsed` and `finPrime` (`c` to `out` first).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

/-- `zeroOut`: `k` zeros to `out`. -/
theorem zeroOut_ok {s : State} {B : Addr} {Z k : Nat} {op : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.rsi, .rcx, .rax] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl kOut (by decide), hl kLen (by decide), hO, hK]) rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := k) (by omega) (FailInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j _ hj t hI
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
  have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
      t'.zf = some (decide (j + 1 = k))) (by
    xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
      ofNat64_pred (show 1 ≤ k - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega)]
    exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
    fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
      exact hI.bytes i (by omega)
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

/-- What an end leaves: the status `st` returned, `u` at `used`, the saved
registers restored, and memory outside the scratch space and `used`
unchanged. -/
structure FinPost (s t : State) (B : Addr) (Z : Nat) (up : Addr) (st u : Nat) : Prop where
  rax : t.gpr .rax = BitVec.ofNat 64 st
  used : t.mem.readW up 64 = BitVec.ofNat 64 u
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)
  frame : ∀ x, Z ≤ ofs B x → (∀ b < 8, x ≠ up + BitVec.ofNat 64 b) → t.mem x = s.mem x
  keep : Keep mmRegs s t

theorem addr_of_sub (x up : Addr) : x = up + BitVec.ofNat 64 (x - up).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The 8 octets at `up`, outside the scratch space, do not meet its header. -/
theorem up_sep {B up : Addr} {Z : Nat} (hn : B.toNat + Z ≤ 2 ^ 64) (hZ : 8 * 32 ≤ Z)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) {i : Nat} (hi : i < 32) :
    Mem.Sep (off B (8 * i)) (64 / 8) up (64 / 8) := by
  intro x h1 h2
  have e1 := addr_of_sub x (off B (8 * i))
  have e2 := addr_of_sub x up
  have := hupZ _ h2
  rw [← e2, e1, ofs_off B (by omega)] at this
  omega

theorem finish_eq (st : Nat) : finish st = [.mov .rdx (.mem (hdr kUsedP)), .store (at0 .rdx) .rax,
    .mov32 .rax (.imm (BitVec.ofNat 32 st)), .mov .rbx (.mem (hdr 0)), .mov .rbp (.mem (hdr 1)),
    .mov .r12 (.mem (hdr 2)), .mov .r13 (.mem (hdr 3)), .mov .r14 (.mem (hdr 4)), .mov .r15 (.mem (hdr 5))] := rfl

/-- `finish st` with `u` in `rax`. -/
theorem finish_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} {st u : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hst : st < 2 ^ 31) (hax : s.gpr .rax = BitVec.ofNat 64 u)
    (hU : word s.mem B (8 * kUsedP) = up) (hupw : InRegions s.wr up 8)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) :
    WP isa (.block (finish st)) s (FinPost s · B Z up st u) := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hw : ∀ i < 32, ∀ v : BitVec 64, word (s.mem.writeW up v) B (8 * i) = word s.mem B (8 * i) := fun i hi v =>
    Mem.readW_writeW_sep (up_sep hn hZ hupZ hi) (by decide)
  refine WP.mono (WP.keep [.rdx, .rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 st ∧ t.mem = s.mem.writeW up (BitVec.ofNat 64 u) ∧
      t.gpr .rbx = word s.mem B (8 * 0) ∧ t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧ t.gpr .r15 = word s.mem B (8 * 5)) (by
    rw [finish_eq]
    xrun [State.ea, hdr, at0, hdi, hdrOff, hl kUsedP (by decide), hU, show BitVec.ofInt 64 0 = 0#64 from rfl,
      BitVec.add_zero, hupw, hax, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide),
      hl 4 (by decide), hl 5 (by decide), hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide),
      hw 4 (by decide), hw 5 (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]) rfl) fun t ⟨⟨hax', hm, h0, h1, h2, h3, h4, h5⟩, k⟩ => ⟨hax', ?_, ?_, ?_, k.mono (by decide)⟩
  · rw [hm]; exact Mem.readW_writeW_self64 _ _ _
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x _ hx
    rw [hm]
    refine Mem.write_apply fun h => hx _ h ?_
    exact addr_of_sub x up

/-- `finNone`: 0 to `used`, status 0. -/
theorem finNone_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hU : word s.mem B (8 * kUsedP) = up) (hupw : InRegions s.wr up 8)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) :
    WP isa finNone s (FinPost s · B Z up 0 0) := by
  unfold finNone
  rw [show ∀ l : List Instr, [Instr.mov32 .rax (.imm 0)] ++ l = [.mov32 .rax (.imm 0)] ++ l from fun _ => rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by xrun) rfl)
    fun s₁ ⟨⟨hax, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (finish_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hZ (by decide) hax
    (by rw [hm₁]; exact hU) (by rw [k₁.2.2]; exact hupw) hupZ) fun t h => ?_
  exact ⟨h.rax, h.used, fun i hi => (h.saved i hi).trans (by rw [hm₁]), fun x hx hx' => (h.frame x hx hx').trans
    (by rw [hm₁]), (k₁.trans h.keep).mono (by decide)⟩

/-- `finUsed st`: `kUsed` to `used`, status `st`. -/
theorem finUsed_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} {st u : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z) (hst : st < 2 ^ 31) (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word s.mem B (8 * kUsedP) = up) (hupw : InRegions s.wr up 8)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) :
    WP isa (finUsed st) s (FinPost s · B Z up st u) := by
  have hn := hs.nowrap
  unfold finUsed
  rw [show ∀ l : List Instr, [Instr.mov .rax (.mem (hdr kUsed))] ++ l = [.mov .rax (.mem (hdr kUsed))] ++ l
    from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 u ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * kUsed) (by unfold kUsed sFn; omega), hu]) rfl)
    fun s₁ ⟨⟨hax, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (finish_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hZ hst hax
    (by rw [hm₁]; exact hU) (by rw [k₁.2.2]; exact hupw) hupZ) fun t h => ?_
  exact ⟨h.rax, h.used, fun i hi => (h.saved i hi).trans (by rw [hm₁]), fun x hx hx' => (h.frame x hx hx').trans
    (by rw [hm₁]), (k₁.trans h.keep).mono (by decide)⟩

theorem exit_eq : [Instr.mov32 .rax (.imm 1)] ++ exit = [.mov32 .rax (.imm 1),
    .mov .rbx (.mem (hdr 0)), .mov .rbp (.mem (hdr 1)), .mov .r12 (.mem (hdr 2)), .mov .r13 (.mem (hdr 3)),
    .mov .r14 (.mem (hdr 4)), .mov .r15 (.mem (hdr 5))] := rfl

theorem sxm1'' : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = mask true := by decide

/-- `finPrime`: `c` (`aN`) to the `8 w` octets of `out`, `kUsed` to `used`,
status 1. -/
theorem finPrime_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {op up : Addr} {u : Nat}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 27)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hO : word s.mem B (8 * kOut) = op)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hU : word s.mem B (8 * kUsedP) = up) (hupw : InRegions s.wr up 8)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b))
    (hout : ∀ j < 8 * w, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < 8 * w, Z ≤ ofs B (op + BitVec.ofNat 64 j))
    (hou : ∀ j < 8 * w, ∀ b < 8, op + BitVec.ofNat 64 j ≠ up + BitVec.ofNat 64 b) :
    WP isa finPrime s fun t =>
      (List.range (8 * w)).map (fun i => t.mem (op + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (wv s.mem B (slot w aN) w) (8 * w) ∧
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.mem.readW up 64 = BitVec.ofNat 64 u ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, Z ≤ ofs B x → (∀ b < 8, x ≠ up + BitVec.ofNat 64 b) → (∀ j < 8 * w, x ≠ op + BitVec.ofNat 64 j) →
        t.mem x = s.mem x) ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hw8 : w = (8 * w + 7) / 8 := by omega
  have hZ8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega
  -- `used`, and the arguments of `storeBE`.
  unfold finPrime
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx, .rbx, .rsi, .rcx, .r15] (Q := fun t => t.gpr .rbx = off B (slot w aN) ∧
      t.gpr .rsi = op ∧ t.gpr .rcx = BitVec.ofNat 64 (8 * w) ∧ t.gpr .r15 = mask true ∧
      t.mem = s.mem.writeW up (BitVec.ofNat 64 u)) (by
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl kUsed (by decide), hl kUsedP (by decide), hu, hU,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hupw, hl (sArr aN) (by decide), hl kOut (by decide),
      hl kLen (by decide), hg.hdr.harr aN (by decide), hO, hK, sxm1'']) rfl) fun s₁ ⟨⟨hbx, hsi, hcx, h15, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have hZx₁ : ∀ x, ofs B x < Z → s₁.mem x = s.mem x := fun x hx => by
    rw [hm₁]; refine Mem.write_apply fun h => ?_
    have := hupZ _ h
    rw [← addr_of_sub x up] at this; omega
  have hwv₁ : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    wv_congr fun i hi => Mem.readW_congr fun b hb => hZx₁ _ (by rw [ofs_off B (by omega)]; omega)
  refine WP.seq (WP.mono (storeBE_ok hs₁ hbx hsi hcx h15 (by omega) (by omega) hw8 (by omega)
    (fun j hj => by rw [k₁.2.2]; exact hout j hj) hsep) fun s₂ ⟨hb₂, hf₂, hwr₂, hrd₂, k₂⟩ => ?_)
  simp only [↓reduceIte] at hb₂
  have hZx : ∀ x, ofs B x < Z → s₂.mem x = s.mem x := fun x hx =>
    (hf₂ x fun j hj he => by have := hsep j hj; rw [← he] at this; omega).trans (hZx₁ x hx)
  have hw₂ : ∀ d, d + 8 ≤ Z → word s₂.mem B d = word s.mem B d := fun d hd =>
    Mem.readW_congr fun b hb => hZx _ (by rw [ofs_off B (by omega)]; omega)
  have hs₂ : Scr s₂ B Z := ⟨by rw [hwr₂, k₁.2.2]; exact hg.scr.1, hn⟩
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₂.ld (by have := hdr_lt_slot w 8 hi; omega)
  -- Status 1, and the saved registers.
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.mem = s₂.mem ∧
      t.gpr .rbx = word s₂.mem B (8 * 0) ∧ t.gpr .rbp = word s₂.mem B (8 * 1) ∧ t.gpr .r12 = word s₂.mem B (8 * 2) ∧
      t.gpr .r13 = word s₂.mem B (8 * 3) ∧ t.gpr .r14 = word s₂.mem B (8 * 4) ∧ t.gpr .r15 = word s₂.mem B (8 * 5)) (by
    rw [exit_eq]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide), hl₂ 3 (by decide),
      hl₂ 4 (by decide), hl₂ 5 (by decide)]) rfl) fun t ⟨⟨hax, hm, h0, h1, h2, h3, h4, h5⟩, k⟩ => ⟨?_, hax, ?_, fun i hi => ?_, fun x hx hx' hx'' => ?_,
      ((k₁.trans k₂).trans k).mono (by decide)⟩
  · rw [hm, ← hwv₁, ← hb₂]
  · rw [hm]
    refine (Mem.readW_congr fun b hb => hf₂ _ fun j hj he => hou j hj b hb he.symm).trans ?_
    rw [hm₁]; exact Mem.readW_writeW_self64 _ _ _
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0.trans (hw₂ _ (by omega))
    · exact h1.trans (hw₂ _ (by omega))
    · exact h2.trans (hw₂ _ (by omega))
    · exact h3.trans (hw₂ _ (by omega))
    · exact h4.trans (hw₂ _ (by omega))
    · exact h5.trans (hw₂ _ (by omega))
  · rw [hm, hf₂ x hx'', hm₁]
    exact Mem.write_apply fun h => hx' _ h (addr_of_sub x up)

end VG.Proof.RsaKeyGen.X86_64
