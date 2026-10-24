module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSave

/-!
# DSA verification on PPC64LE: the contract on the registers, and the entry

`vContract`: `vg_dsa_verify(key = r3, key_len = r4, p_len = r5, q_len = r6,
signature = r7, signature_len = r8, digest = r9, digest_len = r10, scratch,
scratch_len)`, the last two on the stack. `front_ok`: `entry` loads
`scratch`'s address from the stack, saves the nonvolatile registers in its
header, keeps the arguments there (`Hdr`, the digest's length) and lays out
the working spaces.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The arguments on the stack: `scratch` and `scratch_len`. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- `vg_dsa_verify`, on the registers and the stack. -/
def vContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sg : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let dg : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64 ∧ s.rd = [key, sg, dg, stackArgs s] ∧ s.wr = [scr] ∧
      key.Disjoint scr ∧ sg.Disjoint scr ∧ dg.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = 3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat ∧
      (s.gpr .r8).toNat = 2 * (s.gpr .r6).toNat ∧ Spec.Dsa.scratchWords (s.gpr .r5).toNat ≤ (stackArg s 1).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = if Spec.Dsa.verifyBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .r5).toNat (s₁.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat) ++
        [if Spec.Dsa.verifyBytes (s₁.gpr .r5).toNat (s₁.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat)
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r7) (s₁.gpr .r8).toNat)
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r9) (s₁.gpr .r10).toNat) then 1 else 0] =
      Spec.Dsa.publicBytesLeak (s₂.gpr .r5).toNat (s₂.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat) ++
        [if Spec.Dsa.verifyBytes (s₂.gpr .r5).toNat (s₂.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat)
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r7) (s₂.gpr .r8).toNat)
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r9) (s₂.gpr .r10).toNat) then 1 else 0]

/-- A call's layout. -/
def layOf (s : State) : Lay := ⟨stackArg s 0, (stackArg s 1).toNat * 8, (s.gpr .r5).toNat, (s.gpr .r6).toNat⟩

theorem layOf_ok {s : State} (h : vContract.pre s) : (layOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [layOf]; omega, by simp only [layOf]; omega, by simp only [layOf]; omega, nw⟩

/-- The registers `entry` writes. -/
def entryRegs : List Reg := [.r4, .r6, .r11, .r21]

theorem front_off0 (S : Addr) : off S 0 = S := BitVec.add_zero S

/-- A word apart from a later write. -/
theorem front_rd {m : Mem} {S : Addr} {d e : Nat} (v : BitVec 64) (h : e + 8 ≤ d ∨ d + 8 ≤ e)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) : word (m.writeW (off S d) v) S e = word m S e :=
  (writeW_outside m S v hd).word h he

theorem front_rd0 {m : Mem} {S : Addr} {e : Nat} (v : BitVec 64) (h : 8 ≤ e) (he : e + 8 ≤ 2 ^ 64) :
    word (m.writeW S v) S e = word m S e := by
  have := front_rd (m := m) (S := S) (d := 0) v (.inr h) (by decide) he
  rwa [front_off0] at this

theorem front_out {m : Mem} {S : Addr} {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 64) :
    Outside S 0 64 m (m.writeW (off S d) v) :=
  (writeW_outside m S v (by omega)).mono (Nat.zero_le _) (by omega)

/-- The first store, at `S`. -/
theorem front_mem0 (m : Mem) (S : Addr) (v : BitVec 64) :
    word (m.writeW S v) S 0 = v ∧ (∀ e, 8 ≤ e → e + 8 ≤ 2 ^ 64 → word (m.writeW S v) S e = word m S e) ∧
      Outside S 0 64 m (m.writeW S v) := by
  have h := word_writeW_self m S 0 v
  have h' := fun e (h1 : 8 ≤ e) (h2 : e + 8 ≤ 2 ^ 64) => front_rd (m := m) (S := S) (d := 0) v (.inr h1) (by decide) h2
  have h'' := front_out (m := m) (S := S) (d := 0) v (by decide)
  rw [front_off0] at h h' h''
  exact ⟨h, h', h''⟩

/-- The header's eight stores. -/
theorem front_mem {m m₀ m' : Mem} {S : Addr} {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : BitVec 64}
    (h₀ : word m₀ S 0 = v₀ ∧ (∀ e, 8 ≤ e → e + 8 ≤ 2 ^ 64 → word m₀ S e = word m S e) ∧ Outside S 0 64 m m₀)
    (hm : m' = ((((((m₀.writeW (off S 16) v₁).writeW (off S 40) v₂).writeW (off S 48) v₃).writeW
      (off S 56) v₄).writeW (off S 8) v₅).writeW (off S 24) v₆).writeW (off S 32) v₇) :
    (word m' S 0 = v₀ ∧ word m' S 16 = v₁ ∧ word m' S 40 = v₂ ∧ word m' S 48 = v₃ ∧ word m' S 56 = v₄ ∧
      word m' S 8 = v₅ ∧ word m' S 24 = v₆ ∧ word m' S 32 = v₇) ∧
    (∀ e, 64 ≤ e → e + 8 ≤ 2 ^ 64 → word m' S e = word m S e) ∧ Outside S 0 64 m m' := by
  subst hm
  obtain ⟨w0, we, wo⟩ := h₀
  refine ⟨?_, fun e h1 h2 => ?_, ?_⟩
  · simp (disch := decide) only [front_rd, word_writeW_self, w0, and_self]
  · simp (disch := omega) only [front_rd]
    exact we e (by omega) h2
  · exact (((((((wo.trans (front_out _ (by decide))).trans (front_out _ (by decide))).trans
      (front_out _ (by decide))).trans (front_out _ (by decide))).trans (front_out _ (by decide))).trans
      (front_out _ (by decide))).trans (front_out _ (by decide)))

theorem front_q (S x : BitVec 64) :
    28#64 * x + 704#64 + S = S + BitVec.ofNat 64 (704 + 28 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem front_buf (S x : BitVec 64) :
    28#64 * x + 704#64 + S + 1600#64 = S + BitVec.ofNat 64 (704 + 28 * x.toNat + 1600) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem front_saved_ne11 : ∀ i < 18, saved i ≠ .r11 := by decide

/-- The header stores and `layout`, from `S` in `r21`. -/
theorem front_tail {s : State} {S : Addr} {Z : Nat} (h21 : s.gpr .r21 = S) (hs : Scr s S Z) (hZ : 256 ≤ Z) :
    WP isa (.block ([.store .d .r3 .r21 hKey, .store .d .r6 .r21 hQ, .store .d .r7 .r21 hSig,
      .store .d .r9 .r21 hDig, .store .d .r10 .r21 hDlen, .addi .r6 .r5 0] ++ layout)) s fun t =>
      ((word t.mem S 0 = s.gpr .r3 ∧ word t.mem S 16 = s.gpr .r6 ∧ word t.mem S 40 = s.gpr .r7 ∧
        word t.mem S 48 = s.gpr .r9 ∧ word t.mem S 56 = s.gpr .r10 ∧ word t.mem S 8 = s.gpr .r5 ∧
        word t.mem S 24 = 28#64 * s.gpr .r5 + 704#64 + S ∧
        word t.mem S 32 = 28#64 * s.gpr .r5 + 704#64 + S + 1600#64) ∧
      (∀ e, 64 ≤ e → e + 8 ≤ 2 ^ 64 → word t.mem S e = word s.mem S e) ∧ Outside S 0 64 s.mem t.mem) ∧
      Keep [.r6, .r4] s t := by
  refine WP.keep _ ?_ (by decide)
  have st : ∀ d, d + 8 ≤ Z → InRegions s.wr (S + BitVec.ofNat 64 d) 8 := fun d hd => hs.st hd
  have st0 : InRegions s.wr S 8 := by simpa [off] using hs.st (d := 0) (by omega)
  unfold layout
  prun [h21, hKey, hQ, hSig, hDig, hDlen, hP, hQws, hBuf, BitVec.add_zero, st0, st 8 (by omega),
    st 16 (by omega), st 24 (by omega), st 32 (by omega), st 40 (by omega), st 48 (by omega), st 56 (by omega)]
  have := front_mem (v₁ := s.gpr .r6) (v₂ := s.gpr .r7) (v₃ := s.gpr .r9) (v₄ := s.gpr .r10) (v₅ := s.gpr .r5)
    (v₆ := 28#64 * s.gpr .r5 + 704#64 + S) (v₇ := 28#64 * s.gpr .r5 + 704#64 + S + 1600#64)
    (front_mem0 s.mem S (s.gpr .r3)) rfl
  exact ⟨this.1, fun e h1 h2 => this.2.1 e h1 (by omega), this.2.2⟩

/-- `entry`: `scratch` (from the stack) into `r21`, the nonvolatile registers
saved in its header, and the arguments kept there. Memory changes only in
the header. -/
theorem front_ok {s : State} (h : vContract.pre s) :
    WP isa (.block Verify.entry) s fun t =>
      (t.gpr .r21 = stackArg s 0 ∧ ScrL t (layOf s) ∧ Hdr t.mem (layOf s) (s.gpr .r3) (s.gpr .r7) (s.gpr .r9) ∧
        word t.mem (stackArg s 0) hDlen = s.gpr .r10 ∧
        (∀ i < 18, word t.mem (stackArg s 0) (saveOff i) = s.gpr (saved i)) ∧
        Outside (stackArg s 0) 0 256 s.mem t.mem) ∧ Keep entryRegs s t := by
  have hL := layOf_ok h
  have hZ := hL.z256
  obtain ⟨-, hrd, hwr, -, -, -, -, -, -, -, nw, -, -, -, -⟩ := h
  unfold Verify.entry
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (Pub.loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp),
    by simp [Region.Contains]⟩) fun s₁ ⟨⟨a11, m1, _⟩, k1⟩ => ?_)
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (layOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [layOf]) nw
  have hin : ∀ i < 18, InRegions s₁.wr (off (savW (s₁.gpr .r11)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq, a11]
    exact (hscr s₁ k1.wr).st (d := 112 + 8 * i) (by simp only [layOf] at hZ ⊢; omega)
  refine WP.block_append (WP.mono (save_ok s₁ hin) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have h21 : s₂.gpr .r21 = stackArg s 0 := hS.r21.trans a11
  refine WP.mono (front_tail h21 (hscr s₂ (k12.wr)) hZ) fun t ⟨⟨⟨w0, w16, w40, w48, w56, w8, w24, w32⟩, wf, wo⟩, kt⟩ => ?_
  have k := k12.trans kt
  have e : ∀ r, r ≠ .r11 → r ≠ .r21 → s₂.gpr r = s.gpr r := fun r h1 h2 =>
    k12.gpr r fun hm => by
      simp only [List.mem_append, List.mem_singleton] at hm
      exact hm.elim h1 h2
  have qo := hL.qOff_eq
  simp only [layOf] at qo
  refine ⟨⟨(kt.gpr .r21 (by decide)).trans h21, hscr t k.wr, ⟨w0.trans (e _ (by decide) (by decide)),
    w8.trans ?_, w16.trans (e _ (by decide) (by decide)), w24.trans ?_, w32.trans ?_,
    w40.trans (e _ (by decide) (by decide)), w48.trans (e _ (by decide) (by decide))⟩,
    w56.trans (e _ (by decide) (by decide)), fun i hi => ?_, ?_⟩, k.mono⟩
  · rw [e _ (by decide) (by decide)]
    exact BitVec.eq_of_toNat_eq (by simp [layOf])
  · rw [e _ (by decide) (by decide), front_q]
    simp only [Lay.Q, layOf, qo]
  · rw [e _ (by decide) (by decide), front_buf]
    simp only [Lay.Buf, Lay.bOff, layOf, qo]
  · rw [wf _ (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)]
    show s₂.mem.readW (stackArg s 0 + BitVec.ofNat 64 (112 + 8 * i)) 64 = _
    rw [saveOff_eq, ← a11, hS.saved i hi]
    exact k1.gpr _ fun h => front_saved_ne11 i hi (List.mem_singleton.mp h)
  · have f2 : Outside (stackArg s 0) 112 144 s₁.mem s₂.mem :=
      VG.Proof.Bignum.frame_outside (by rw [← a11]; exact hS.frame) (by decide)
    rw [← m1]
    exact (f2.mono (Nat.zero_le _) (by decide)).trans (wo.mono (Nat.le_refl _) (by decide))

end VG.Proof.Dsa.PPC64LE
