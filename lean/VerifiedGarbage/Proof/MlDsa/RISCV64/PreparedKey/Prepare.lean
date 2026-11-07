module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.MlDsa.RISCV64.CacheCopy
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Contracts
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Steps
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Site
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.ContractsV
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.MlDsa.RISCV64.PreparedKey.Prepare
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# ML-DSA on RISC-V: preparing keys

The body of `vg_mldsa*_prepare_verifying_key` and `vg_mldsa*_prepare_signing_key`
(`prepBody`, `Impl/MlDsa/RISCV64/PreparedKey/Prepare.lean`), given the buffer
in `a3`: it saves our caller's `s8`–`s11` and the return address in the
buffer at 1024 and moves the arguments into them (`Inv`, Ed25519's whole
functions' invariant); copies the key to `prepared` (`PI … 0`); then, for each
polynomial `i`, decodes it into the buffer, transforms it in place and copies
it after the key (`PI … (i + 1)`), each step writing only `prepared`, `scratch`
and the buffer's first 1024 bytes; and restores the registers. Two runs whose
pointers agree leak the same: the moves and copies are at the pointers, and
the calls leak what their contracts permit. With the buffer in a frame on the
stack (`withStackScratchWiped`), the functions meet their contracts.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PreparedKey

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Spec.MlDsa
open VG.Impl.MlDsa.RISCV64.PreparedKey
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg callAt seqR glue)
open VG.Impl.MlDsa.RISCV64.CacheCopy (copyN)
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.RISCV64.Whole (Inv slotArea restore_ok restoreList)
open VG.Proof.MlDsa.RISCV64.KeyGen (glueOk glueSt argVal callV callV_tr CallRel view Piece Rel2 rel_of)
open VG.Proof.MlDsa (PolyIs Reduced polyAt)
open VG.Spec.Sha3 (bytesAt)

/-! ## The arguments -/

section
variable (σ : State)

abbrev pK : Addr := σ.gpr .a0
abbrev pO : Addr := σ.gpr .a1
abbrev pC : Addr := σ.gpr .a2
abbrev pB : Addr := σ.gpr .a3

/-- What the kept registers hold. -/
def pv : Reg → BitVec 64
  | .s8 => pC σ | .s9 => pO σ | .s10 => pK σ | .s11 => pB σ | _ => 0

/-- What the body writes. -/
abbrev pW (ol : Nat) : List Region := [⟨pO σ, ol⟩, ⟨pC σ, 1024⟩, ⟨pB σ, 1072⟩]

end

/-- The body's precondition (with the key's length `kl` and `prepared`'s `ol`). -/
structure PPre (kl ol : Nat) (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  rd : s.rd = [⟨pK s, kl⟩]
  wr : s.wr = [⟨pO s, ol⟩, ⟨pC s, 1024⟩, ⟨pB s, 1072⟩]
  d01 : Region.Disjoint ⟨pK s, kl⟩ ⟨pO s, ol⟩
  d02 : Region.Disjoint ⟨pK s, kl⟩ ⟨pC s, 1024⟩
  d03 : Region.Disjoint ⟨pK s, kl⟩ ⟨pB s, 1072⟩
  d12 : Region.Disjoint ⟨pO s, ol⟩ ⟨pC s, 1024⟩
  d13 : Region.Disjoint ⟨pO s, ol⟩ ⟨pB s, 1072⟩
  d23 : Region.Disjoint ⟨pC s, 1024⟩ ⟨pB s, 1072⟩
  f0 : (pK s).toNat + kl ≤ 2 ^ 64
  f1 : (pO s).toNat + ol ≤ 2 ^ 64
  f2 : (pC s).toNat + 1024 ≤ 2 ^ 64
  f3 : (pB s).toNat + 1072 ≤ 2 ^ 64
  al2 : (pC s).toNat % 8 = 0
  al3 : (pB s).toNat % 8 = 0

/-- What two runs agree on: the stack pointer and the pointers. -/
def PPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ pK s₁ = pK s₂ ∧ pO s₁ = pO s₂ ∧ pC s₁ = pC s₂ ∧ pB s₁ = pB s₂

/-- The sizes: `n` polynomials after a key of `kl` bytes. -/
structure PSizes (kl ol n : Nat) : Prop where
  eq : ol = kl + 1024 * n
  lt : ol < 2 ^ 31 - 2048

/-- After the saves and moves. -/
abbrev PS (ol : Nat) (σ t : State) : Prop := Inv σ (pB σ) oSV keptRegs (pv σ) (pW σ ol) t

/-- After the key and the first `i` polynomials. -/
structure PI (kl ol : Nat) (F : State → Nat → Poly) (i : Nat) (σ t : State) : Prop where
  inv : PS ol σ t
  out : bytesAt t.mem (pO σ) kl = bytesAt σ.mem (pK σ) kl
  polys : ∀ j < i, PolyIs t.mem (pO σ + BitVec.ofNat 64 (kl + 1024 * j)) (F σ j)

/-! ## Regions -/

theorem keptRegs_pres : ∀ r ∈ keptRegs, r ∈ preserved := by decide

theorem sub_zero (b : Addr) (R : Region) : Region.Sub ⟨b, 0⟩ R := fun x hx => by
  simp only [Region.Contains] at hx; omega

theorem disj_zero (b : Addr) (R : Region) : Region.Disjoint R ⟨b, 0⟩ := fun x _ hx => by
  simp only [Region.Contains] at hx; omega

section
variable {kl ol n : Nat} (hz : PSizes kl ol n) {σ t : State} (hp : PPre kl ol σ)
include hz hp

omit hz hp in
theorem regs_of (h : PS ol σ t) :
    t.gpr .s8 = pC σ ∧ t.gpr .s9 = pO σ ∧ t.gpr .s10 = pK σ ∧ t.gpr .s11 = pB σ :=
  ⟨h.regs _ (by decide), h.regs _ (by decide), h.regs _ (by decide), h.regs _ (by decide)⟩

omit hz in
/-- The key, which the body does not write. -/
theorem key_keep (h : PS ol σ t) {o l : Nat} (hl : o + l ≤ kl) :
    bytesAt t.mem (pK σ + BitVec.ofNat 64 o) l = bytesAt σ.mem (pK σ + BitVec.ofNat 64 o) l := by
  have := hp.f0
  have hsub : Region.Sub ⟨pK σ + BitVec.ofNat 64 o, l⟩ ⟨pK σ, kl⟩ := Offset.sub_base _ hl
  refine Proof.MlKem.bytesAt_frame h.frame (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.d01.sub_left hsub
  · exact hp.d02.sub_left hsub
  · exact hp.d03.sub_left hsub

omit hz in
/-- The buffer's polynomial is apart from the slots. -/
theorem buf_slots : Region.Disjoint (slotArea (pB σ) oSV keptRegs) ⟨pB σ, 1024⟩ := by
  have := hp.f3
  exact (Offset.base_disjoint (pB σ) (e := 1024) (n := 40) (k := 1024) (by omega) (by omega)).symm

omit hz in
theorem out_slots {o l : Nat} (h : o + l ≤ ol) :
    Region.Disjoint (slotArea (pB σ) oSV keptRegs) ⟨pO σ + BitVec.ofNat 64 o, l⟩ :=
  (hp.d13.sub_left (Offset.sub_base _ h)).symm.sub_left
    (Offset.sub_base (pB σ) (d := 1024) (n := 40) (k := 1072) (by decide))

omit hz in
theorem scr_slots : Region.Disjoint (slotArea (pB σ) oSV keptRegs) ⟨pC σ, 1024⟩ :=
  hp.d23.symm.sub_left (Offset.sub_base (pB σ) (d := 1024) (n := 40) (k := 1072) (by decide))

end

/-! ## The saves and the key -/

section
variable {kl ol n : Nat} (hz : PSizes kl ol n) {F : State → Nat → Poly}
include hz

omit hz in
theorem setup_wp {σ : State} (hp : PPre kl ol σ) : WP isa (.block prepEnter) σ (PS ol σ) := by
  unfold prepEnter
  rw [← List.append_nil (saveRegs .a3 oSV keptRegs ++ _)]
  refine Message.setup_ok (f := .a3) (o := oSV) (rs := keptRegs)
    (ms := [(.s8, .a2), (.s9, .a1), (.s10, .a0), (.s11, .a3)]) (v := pv σ) (W := pW σ ol)
    hp.al3 (by decide) (by decide) (fun q hq => ?_) ⟨⟨pB σ, 1072⟩, by simp, Offset.sub_base _ (by decide)⟩ rfl
    (by decide) (by decide) (fun q hq => ?_) fun u hu _ => WP.block_nil hu
  · have h1 : q.2 + 8 ≤ 1064 := by
      have := (Proof.Ed25519.RISCV64.Whole.slots_in oSV keptRegs q hq).2
      simpa [oSV, keptRegs] using this
    have := hp.f3
    exact ⟨⟨pB σ, 1072⟩, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> rfl

omit hz in
theorem copy_glue (hl : kl < 2 ^ 31 - 2048) :
    glueOk [(.a0, .ptr (.s10, 0)), (.a1, .ptr (.s9, 0)), (.a2, .imm kl)] = true := by
  simp [glueOk, KeyGen.argReg, KeyGen.argOk]
  omega

omit hz in
/-- A step that keeps the callee-saved registers, writes within `Wc` and keeps the slots. -/
theorem ps_step {σ t t' : State} (h : PS ol σ t) {Wc : List Region} (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hf : Frame Wc t.mem t'.mem)
    (hsub : ∀ r ∈ Wc, ∃ R ∈ pW σ ol, Region.Sub r R)
    (hd : ∀ r ∈ Wc, Region.Disjoint (slotArea (pB σ) oSV keptRegs) r) : PS ol σ t' :=
  Inv.step h keptRegs_pres hrd hwr hsp hg hf hsub hd

theorem keyCopy_wp {σ t : State} (hp : PPre kl ol σ) (hk : 0 < kl) (h : PS ol σ t) :
    WP isa (copyN (.s10, 0) (.s9, 0) kl) t (PI kl ol F 0 σ) := by
  have := hz.eq; have := hz.lt; have := hp.f0; have := hp.f1
  obtain ⟨g8, g9, g10, g11⟩ := regs_of h
  have hrd : t.rd = σ.rd := h.rd
  have hwr : t.wr = σ.wr := h.wr
  have hs : t.gpr (Reg.s10, 0).1 + BitVec.ofNat 64 (Reg.s10, 0).2 = pK σ := by
    show t.gpr .s10 + _ = _; rw [g10, BitVec.add_zero]
  have hd : t.gpr (Reg.s9, 0).1 + BitVec.ofNat 64 (Reg.s9, 0).2 = pO σ := by
    show t.gpr .s9 + _ = _; rw [g9, BitVec.add_zero]
  have osub : Region.Sub ⟨pO σ, kl⟩ ⟨pO σ, ol⟩ := by
    have e := Offset.sub_base (pO σ) (d := 0) (n := kl) (k := ol) (by omega)
    rwa [BitVec.add_zero] at e
  refine WP.mono (CacheCopy.copyN_ok (src := (.s10, 0)) (dst := (.s9, 0)) (len := kl) (copy_glue (by omega)) hk (s := t)
    (by rw [hs, hd]; exact hp.d01.sub_right osub)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [hs, hrd, hp.rd]; exact ⟨⟨pK σ, kl⟩, by simp, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [hd, hwr, hp.wr]; exact ⟨⟨pO σ, ol⟩, by simp, 0, by simp, by simp; omega⟩))
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [hd] at fr
    refine ps_step h rd wr sp cs fr (fun r hr => ?_) fun r hr => ?_ <;>
      rw [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, by simp, osub⟩
    · have := out_slots hp (o := 0) (l := kl) (by omega)
      rwa [BitVec.add_zero] at this
  · rw [hs, hd] at hb
    rw [hb]
    have := key_keep hp h (o := 0) (l := kl) (by omega)
    rwa [BitVec.add_zero] at this

end

/-! ## The polynomials -/

theorem ntt_sd : sdepth Impl.MlDsa.RISCV64.Arith.ntt = 0 := by decide +kernel
theorem t1_sd : sdepth Impl.MlDsa.RISCV64.Pack.unpackT1 = 0 := by decide +kernel
theorem bu_sd : sdepth Impl.MlDsa.RISCV64.Pack.bitUnpack = 0 := by decide +kernel

/-- A region's prefix. -/
theorem pre_sub (b : Addr) {a c : Nat} (h : a ≤ c) : Region.Sub ⟨b, a⟩ ⟨b, c⟩ := by
  have e := Offset.sub_base b (d := 0) (n := a) (k := c) (by omega)
  rwa [BitVec.add_zero] at e

theorem zero_disj (b : Addr) (R : Region) : Region.Disjoint ⟨b, 0⟩ R := fun x hx _ => by
  simp only [Region.Contains] at hx; omega

theorem cov_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  Covers.of_sub fun r hr => ⟨r, h r hr, 0, (BitVec.add_zero _).symm, by omega⟩

theorem garg {t : State} {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup)
    {d : Reg} {a : Arg} (hm : (d, a) ∈ as) (hl : d ∉ VG.RISCV64.linkRegs) (rd wr : List Region) :
    (view (glueSt t as) rd wr).gpr d = argVal t a := by
  rw [KeyGen.view_gpr _ _ _ hl, KeyGen.glueSt_arg t hg hn hm]

/-- The calls' arguments and regions. -/
abbrev nttArgs : List (Reg × Arg) := [(.a0, .ptr (.s11, 0)), (.a1, .ptr (.s8, 0))]
abbrev t1Args (o : Nat) : List (Reg × Arg) := [(.a0, .ptr (.s10, o)), (.a1, .ptr (.s11, 0))]
abbrev buArgs (o len a b : Nat) : List (Reg × Arg) :=
  [(.a0, .ptr (.s10, o)), (.a1, .imm len), (.a2, .imm a), (.a3, .imm b), (.a4, .ptr (.s11, 0))]
abbrev nttW (σ : State) : List Region := [⟨pB σ, 1024⟩, ⟨pC σ, 1024⟩]
abbrev bufW (σ : State) : List Region := [⟨pB σ, 1024⟩]
abbrev keyR (σ : State) (o l : Nat) : List Region := [⟨pK σ + BitVec.ofNat 64 o, l⟩]

theorem ntt_hg : glueOk nttArgs = true := by decide
theorem ntt_hn : (nttArgs.map Prod.fst).Nodup := by simp
theorem t1_hg {o : Nat} (ho : o < 2 ^ 31 - 2048) : glueOk (t1Args o) = true := by
  simp [glueOk, KeyGen.argReg, KeyGen.argOk]; omega
theorem t1_hn (o : Nat) : ((t1Args o).map Prod.fst).Nodup := by simp
theorem bu_hg {o len a b : Nat} (ho : o < 2 ^ 31 - 2048) (hl : len < 2 ^ 31 - 2048) (ha : a < 2 ^ 31 - 2048)
    (hb : b < 2 ^ 31 - 2048) : glueOk (buArgs o len a b) = true := by
  simp [glueOk, KeyGen.argReg, KeyGen.argOk]; omega
theorem bu_hn (o len a b : Nat) : ((buArgs o len a b).map Prod.fst).Nodup := by simp

section
variable {kl ol n : Nat} (hz : PSizes kl ol n) {F : State → Nat → Poly} {σ : State} (hp : PPre kl ol σ)
include hz hp

omit hp in
/-- A step that writes within `Wc`, apart from the key's copy and the first `i` polynomials. -/
theorem pi_keep {i : Nat} (hi : i ≤ n) {t t' : State} (h : PI kl ol F i σ t) {Wc : List Region}
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r)
    (hf : Frame Wc t.mem t'.mem) (hsub : ∀ r ∈ Wc, ∃ R ∈ pW σ ol, Region.Sub r R)
    (hd : ∀ r ∈ Wc, Region.Disjoint (slotArea (pB σ) oSV keptRegs) r)
    (ho : ∀ r ∈ Wc, Region.Disjoint ⟨pO σ, kl + 1024 * i⟩ r) : PI kl ol F i σ t' := by
  have := hz.eq; have := hz.lt
  refine ⟨ps_step h.inv hrd hwr hsp hg hf hsub hd, ?_, fun j hj => ?_⟩
  · have hs : Region.Sub ⟨pO σ, kl⟩ ⟨pO σ, kl + 1024 * i⟩ := pre_sub _ (by omega)
    rw [Proof.MlKem.bytesAt_frame hf (fun r hr => (ho r hr).sub_left hs) (by omega)]
    exact h.out
  · exact Arith.polyIs_frame hf (fun r hr => (ho r hr).sub_left
      (Offset.sub_base (pO σ) (d := kl + 1024 * j) (n := 1024) (k := kl + 1024 * i) (by omega))) (h.polys j hj)

omit hp in
/-- What a callee may write: within `pW`, apart from the slots, the key's copy and the polynomials. -/
theorem callee_keep {i : Nat} (hi : i ≤ n) {t t' : State} (h : PI kl ol F i σ t) {wr : List Region} {k : Nat}
    (hk0 : k = 0) (hk : Proof.MlKem.RISCV64.Kept (wr ++ [below t.sp k]) t t') (hsub : ∀ r ∈ wr, ∃ R ∈ pW σ ol, Region.Sub r R)
    (hd : ∀ r ∈ wr, Region.Disjoint (slotArea (pB σ) oSV keptRegs) r)
    (ho : ∀ r ∈ wr, Region.Disjoint ⟨pO σ, kl + 1024 * i⟩ r) : PI kl ol F i σ t' := by
  subst hk0
  refine pi_keep hz hi h hk.rd hk.wr hk.sp hk.cs hk.frame (fun r hr => ?_) (fun r hr => ?_) fun r hr => ?_ <;>
    rcases List.mem_append.mp hr with hr | hr
  · exact hsub r hr
  · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_zero _ _⟩
  · exact hd r hr
  · rw [List.mem_singleton] at hr; subst hr; exact disj_zero _ _
  · exact ho r hr
  · rw [List.mem_singleton] at hr; subst hr; exact disj_zero _ _

/-- The buffer's polynomial, apart from the key's copy and the polynomials. -/
theorem buf_out {i : Nat} (hi : i ≤ n) : Region.Disjoint ⟨pO σ, kl + 1024 * i⟩ ⟨pB σ, 1024⟩ := by
  have := hz.eq
  exact (hp.d13.sub_left (pre_sub (pO σ) (by omega))).sub_right
    (pre_sub (pB σ) (by decide))

omit hz in
/-- The writable regions, at an offset in them. -/
theorem cov_w {t : State} (h : PS ol σ t) {rs : List Region}
    (hr : ∀ r ∈ rs, ∃ r' ∈ pW σ ol, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len) :
    Covers rs t.wr ∧ Covers rs (t.rd ++ t.wr) := by
  rw [h.wr, hp.wr]
  refine ⟨Covers.of_sub hr, Covers.of_sub fun r hm => ?_⟩
  obtain ⟨r', h', o, e, l⟩ := hr r hm
  exact ⟨r', List.mem_append_right _ h', o, e, l⟩

omit hz hp in
/-- The buffer and `scratch`, in two runs. -/
theorem ntt_regs {t : State} (h : PS ol σ t) (rd wr : List Region) :
    (view (glueSt t nttArgs) rd wr).gpr .a0 = pB σ ∧ (view (glueSt t nttArgs) rd wr).gpr .a1 = pC σ := by
  obtain ⟨g8, -, -, g11⟩ := regs_of h
  refine ⟨?_, ?_⟩
  · rw [garg ntt_hg ntt_hn (d := .a0) (a := .ptr (.s11, 0)) (by simp) (by decide)]
    simp only [argVal, g11, BitVec.add_zero]
  · rw [garg ntt_hg ntt_hn (d := .a1) (a := .ptr (.s8, 0)) (by simp) (by decide)]
    simp only [argVal, g8, BitVec.add_zero]

omit hz in
theorem ntt_call {t : State} (h : PS ol σ t) (hr : Reduced t.mem (pB σ)) :
    (Proof.MlDsa.nttContract RISCV64.abi).pre (view (glueSt t nttArgs) [] (nttW σ)) ∧
      Covers ([] ++ nttW σ) (t.rd ++ t.wr) ∧ Covers (nttW σ) t.wr := by
  have := hp.f2; have := hp.f3; have := hp.al3
  obtain ⟨e0, e1⟩ := ntt_regs h [] (nttW σ)
  have bsub : Region.Sub ⟨pB σ, 1024⟩ ⟨pB σ, 1072⟩ := pre_sub _ (by omega)
  obtain ⟨c1, c2⟩ := cov_w hp (rs := nttW σ) h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨pB σ, 1072⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨pC σ, 1024⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  exact ⟨KeyGen.ip_pre (stk := 0) e0 e1 rfl rfl (Nat.zero_le _)
    (by rw [KeyGen.view_glue_sp, h.sp]; exact hp.al) (by omega) hp.al2
    (hp.d23.symm.sub_left bsub) (zero_disj _ _) (zero_disj _ _) (by omega) (by omega)
    (by rw [KeyGen.view_glue_mem]; exact hr), by simpa using c2, c1⟩

/-- The buffer's polynomial transformed. -/
theorem ntt_wp {i : Nat} (hi : i < n) {t : State} (h : PI kl ol F i σ t) {g : Poly}
    (hb : PolyIs t.mem (pB σ) g) {Q : State → Prop}
    (hQ : ∀ t', PI kl ol F i σ t' → PolyIs t'.mem (pB σ) (ntt g) → Q t') :
    WP isa (callAt "vg_mldsa_ntt" Impl.MlDsa.RISCV64.Arith.ntt nttArgs) t Q := by
  have := hz.eq; have := hp.f3
  have bsub : Region.Sub ⟨pB σ, 1024⟩ ⟨pB σ, 1072⟩ := pre_sub _ (by omega)
  obtain ⟨cp, c2, c1⟩ := ntt_call hp h.inv hb.1
  refine callV Arith.Ntt.verified.1 (by rw [ntt_sd]; decide) ntt_hg cp c2 c1
    fun t' k hpost => hQ t' (callee_keep hz (Nat.le_of_lt hi) h ntt_sd k (fun r hr => ?_) (fun r hr => ?_)
      (fun r hr => ?_)) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, bsub⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact buf_slots hp
    · exact scr_slots hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact buf_out hz hp (Nat.le_of_lt hi)
    · exact hp.d12.sub_left (pre_sub _ (by omega))
  · have := KeyGen.ip_post hpost
    rw [(ntt_regs h.inv _ _).1, KeyGen.view_glue_mem, State.withRegions_mem, hb.2] at this
    exact this

/-- The buffer's polynomial copied after the key and the first `i`. -/
theorem copyOut_wp {i : Nat} (hi : i < n) {u : State} (hu : PI kl ol F i σ u) {g : Poly}
    (hbu : PolyIs u.mem (pB σ) g) (hF : F σ i = g) :
    WP isa (copyN (.s11, 0) (.s9, kl + 1024 * i) 1024) u (PI kl ol F (i + 1) σ) := by
  have := hz.eq; have := hz.lt; have := hp.f1; have := hp.f2; have := hp.f3
  have bsub : Region.Sub ⟨pB σ, 1024⟩ ⟨pB σ, 1072⟩ := pre_sub _ (by omega)
  obtain ⟨u8, u9, u10, u11⟩ := regs_of hu.inv
  have hs : u.gpr (Reg.s11, 0).1 + BitVec.ofNat 64 (Reg.s11, 0).2 = pB σ := by
    show u.gpr .s11 + _ = _; rw [u11, BitVec.add_zero]
  have hd : u.gpr (Reg.s9, kl + 1024 * i).1 + BitVec.ofNat 64 (Reg.s9, kl + 1024 * i).2 =
      pO σ + BitVec.ofNat 64 (kl + 1024 * i) := by
    show u.gpr .s9 + _ = _; rw [u9]
  have osub : Region.Sub ⟨pO σ + BitVec.ofNat 64 (kl + 1024 * i), 1024⟩ ⟨pO σ, ol⟩ :=
    Offset.sub_base _ (by omega)
  obtain ⟨-, cr⟩ := cov_w hp (rs := [⟨pB σ, 1024⟩]) hu.inv fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨⟨pB σ, 1072⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  obtain ⟨cw, -⟩ := cov_w hp (rs := [⟨pO σ + BitVec.ofNat 64 (kl + 1024 * i), 1024⟩]) hu.inv fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨⟨pO σ, ol⟩, by simp, kl + 1024 * i, rfl, by simp; omega⟩
  refine WP.mono (CacheCopy.copyN_ok (src := (.s11, 0)) (dst := (.s9, kl + 1024 * i)) (len := 1024)
    (by simp [glueOk, KeyGen.argReg, KeyGen.argOk]; omega) (by decide) (s := u)
    (by rw [hs, hd]; exact (hp.d13.sub_left osub).symm.sub_left bsub)
    (by rw [hs]; exact cr) (by rw [hd]; exact cw))
    fun u' ⟨cs, rd, wr, sp, fr, hbt⟩ => ?_
  rw [hd] at fr hbt
  rw [hs] at hbt
  refine ⟨ps_step hu.inv rd wr sp cs fr (fun r hr => ?_) (fun r hr => ?_), ?_, fun j hj => ?_⟩
  · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩
  · rw [List.mem_singleton] at hr; subst hr; exact out_slots hp (by omega)
  · rw [Proof.MlKem.bytesAt_frame fr (fun r hr => ?_) (by omega)]
    · exact hu.out
    · rw [List.mem_singleton] at hr; subst hr
      exact (Offset.disjoint_base (pO σ) (d := kl + 1024 * i) (n := 1024) (k := kl) (by omega) (by omega)).symm
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · refine Arith.polyIs_frame fr (fun r hr => ?_) (hu.polys j hj)
      rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint (pO σ) (by omega) (by omega) (by omega)
    · rw [hF]
      exact Proof.MlDsa.PreparedKey.polyIs_of_copy hbt hbu

/-- The buffer's polynomial transformed, and copied after the key and the first `i`. -/
theorem nttOut_wp {i : Nat} (hi : i < n) {t : State} (h : PI kl ol F i σ t) {g : Poly}
    (hb : PolyIs t.mem (pB σ) g) (hF : F σ i = ntt g) :
    WP isa (nttOut (kl + 1024 * i)) t (PI kl ol F (i + 1) σ) :=
  WP.seq (ntt_wp hz hp hi h hb fun _ hu hbu => copyOut_wp hz hp hi hu hbu hF)

omit hz in
/-- The key's bytes at `o`, read. -/
theorem cov_r {t : State} (h : PS ol σ t) {o l : Nat} (hl : o + l ≤ kl) (ws : List Region)
    (hw : Covers ws (t.rd ++ t.wr)) : Covers ([⟨pK σ + BitVec.ofNat 64 o, l⟩] ++ ws) (t.rd ++ t.wr) := by
  rw [show [(⟨pK σ + BitVec.ofNat 64 o, l⟩ : Region)] ++ ws = [⟨pK σ + BitVec.ofNat 64 o, l⟩] ++ ws from rfl]
  intro a m ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton] at hr; subst hr
    refine Covers.of_sub (rs := [⟨pK σ + BitVec.ofNat 64 o, l⟩]) (fun r hr => ?_) a m ⟨_, List.mem_singleton_self _, hc⟩
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨⟨pK σ, kl⟩, by rw [h.rd, hp.rd]; simp, o, rfl, by simp; omega⟩
  · exact hw a m ⟨r, hr, hc⟩

omit hz in
theorem key_toNat {o : Nat} (ho : o < kl) : (pK σ + BitVec.ofNat 64 o).toNat = (pK σ).toNat + o := by
  have := hp.f0
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

omit hz hp in
theorem t1_regs {o : Nat} (ho : o < 2 ^ 31 - 2048) {t : State} (h : PS ol σ t) (rd wr : List Region) :
    (view (glueSt t (t1Args o)) rd wr).gpr .a0 = pK σ + BitVec.ofNat 64 o ∧
      (view (glueSt t (t1Args o)) rd wr).gpr .a1 = pB σ := by
  obtain ⟨-, -, g10, g11⟩ := regs_of h
  refine ⟨?_, ?_⟩
  · rw [garg (t1_hg ho) (t1_hn o) (d := .a0) (a := .ptr (.s10, o)) (by simp) (by decide)]
    simp only [argVal, g10]
  · rw [garg (t1_hg ho) (t1_hn o) (d := .a1) (a := .ptr (.s11, 0)) (by simp) (by decide)]
    simp only [argVal, g11, BitVec.add_zero]

theorem t1_call {o : Nat} (ho : o + 320 ≤ kl) {t : State} (h : PS ol σ t) :
    (Proof.MlDsa.unpackT1Contract RISCV64.abi).pre (view (glueSt t (t1Args o)) (keyR σ o 320) (bufW σ)) ∧
      Covers (keyR σ o 320 ++ bufW σ) (t.rd ++ t.wr) ∧ Covers (bufW σ) t.wr := by
  have := hz.eq; have := hz.lt; have := hp.f0; have := hp.f3; have := hp.al3
  obtain ⟨e0, e1⟩ := t1_regs (o := o) (by omega) h (keyR σ o 320) (bufW σ)
  have bsub : Region.Sub ⟨pB σ, 1024⟩ ⟨pB σ, 1072⟩ := pre_sub _ (by omega)
  have ksub : Region.Sub ⟨pK σ + BitVec.ofNat 64 o, 320⟩ ⟨pK σ, kl⟩ := Offset.sub_base _ ho
  obtain ⟨c1, c2⟩ := cov_w hp (rs := bufW σ) h fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨⟨pB σ, 1072⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  exact ⟨KeyGen.t1_pre (stk := 0) e0 e1 rfl rfl (Nat.zero_le _)
    (by rw [KeyGen.view_glue_sp, h.sp]; exact hp.al) (by omega)
    ((hp.d03.sub_left ksub).sub_right bsub) (zero_disj _ _) (zero_disj _ _)
    (by rw [key_toNat hp (by omega)]; omega) (by omega), cov_r hp h ho _ c2, c1⟩

/-- `t₁[i] · 2ᵈ` of the 320 bytes at `o` of the key, decoded into the buffer. -/
theorem t1_wp {i o : Nat} (hi : i ≤ n) (ho : o + 320 ≤ kl) {t : State} (h : PI kl ol F i σ t) {Q : State → Prop}
    (hQ : ∀ t', PI kl ol F i σ t' → PolyIs t'.mem (pB σ)
      ((simpleBitUnpack (bytesAt σ.mem (pK σ + BitVec.ofNat 64 o) 320) t1Max).map
        fun c => ofInt (c * 2 ^ d : Nat)) → Q t') :
    WP isa (callAt "vg_mldsa_unpack_t1" Impl.MlDsa.RISCV64.Pack.unpackT1 (t1Args o)) t Q := by
  have := hz.eq; have := hz.lt; have := hp.f3
  have bsub : Region.Sub ⟨pB σ, 1024⟩ ⟨pB σ, 1072⟩ := pre_sub _ (by omega)
  obtain ⟨cp, c2, c1⟩ := t1_call hz hp ho h.inv
  refine callV Pack.unpackT1_verified.1 (by rw [t1_sd]; decide) (t1_hg (by omega)) cp c2 c1
    fun t' k hpost => hQ t' (callee_keep hz hi h t1_sd k (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_)) ?_
  · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, bsub⟩
  · rw [List.mem_singleton] at hr; subst hr; exact buf_slots hp
  · rw [List.mem_singleton] at hr; subst hr; exact buf_out hz hp hi
  · have := KeyGen.t1_post hpost
    obtain ⟨e0, e1⟩ := t1_regs (o := o) (by omega) h.inv (keyR σ o 320) (bufW σ)
    rw [e0, e1, KeyGen.view_glue_mem, State.withRegions_mem, key_keep hp h.inv ho] at this
    exact this

omit hz hp in
theorem bu_regs {o len a b : Nat} (hg : glueOk (buArgs o len a b) = true) {t : State} (h : PS ol σ t)
    (rd wr : List Region) :
    (view (glueSt t (buArgs o len a b)) rd wr).gpr .a0 = pK σ + BitVec.ofNat 64 o ∧
      (view (glueSt t (buArgs o len a b)) rd wr).gpr .a1 = BitVec.ofNat 64 len ∧
      (view (glueSt t (buArgs o len a b)) rd wr).gpr .a2 = BitVec.ofNat 64 a ∧
      (view (glueSt t (buArgs o len a b)) rd wr).gpr .a3 = BitVec.ofNat 64 b ∧
      (view (glueSt t (buArgs o len a b)) rd wr).gpr .a4 = pB σ := by
  obtain ⟨-, -, g10, g11⟩ := regs_of h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [garg hg (bu_hn ..) (d := .a0) (a := .ptr (.s10, o)) (by simp) (by decide)]; simp only [argVal, g10]
  · rw [garg hg (bu_hn ..) (d := .a1) (a := .imm len) (by simp) (by decide)]; rfl
  · rw [garg hg (bu_hn ..) (d := .a2) (a := .imm a) (by simp) (by decide)]; rfl
  · rw [garg hg (bu_hn ..) (d := .a3) (a := .imm b) (by simp) (by decide)]; rfl
  · rw [garg hg (bu_hn ..) (d := .a4) (a := .ptr (.s11, 0)) (by simp) (by decide)]
    simp only [argVal, g11, BitVec.add_zero]

theorem bu_call {o len a b : Nat} (ho : o + len ≤ kl) (hl0 : 0 < len)
    (hab : (a, b) ∈ Proof.MlDsa.bitPackParams) (hl : len = 32 * bitlen (a + b)) (ha : a < 2 ^ 31 - 2048)
    (hb : b < 2 ^ 31 - 2048) {t : State} (h : PS ol σ t) :
    (Proof.MlDsa.bitUnpackContract RISCV64.abi).pre
        (view (glueSt t (buArgs o len a b)) (keyR σ o len) (bufW σ)) ∧
      Covers (keyR σ o len ++ bufW σ) (t.rd ++ t.wr) ∧ Covers (bufW σ) t.wr := by
  have := hz.eq; have := hz.lt; have := hp.f0; have := hp.f3; have := hp.al3
  obtain ⟨e0, e1, e2, e3, e4⟩ := bu_regs (bu_hg (o := o) (len := len) (by omega) (by omega) ha hb) h (keyR σ o len) (bufW σ)
  have bsub : Region.Sub ⟨pB σ, 1024⟩ ⟨pB σ, 1072⟩ := pre_sub _ (by omega)
  have ksub : Region.Sub ⟨pK σ + BitVec.ofNat 64 o, len⟩ ⟨pK σ, kl⟩ := Offset.sub_base _ ho
  have el : (BitVec.ofNat 64 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  have ea : (BitVec.setWidth 32 (BitVec.ofNat 64 a)).toNat = a := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have eb : (BitVec.setWidth 32 (BitVec.ofNat 64 b)).toNat = b := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  obtain ⟨c1, c2⟩ := cov_w hp (rs := bufW σ) h fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨⟨pB σ, 1072⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  refine ⟨KeyGen.bu_pre (stk := 0) e0 e1 (by rw [e2]) (by rw [e3]) e4 (by rw [el]; rfl) rfl (Nat.zero_le _)
    (by rw [KeyGen.view_glue_sp, h.sp]; exact hp.al) (by omega)
    (by rw [el]; exact (hp.d03.sub_left ksub).sub_right bsub) (zero_disj _ _) (zero_disj _ _)
    (by rw [el, key_toNat hp (by omega)]; omega) (by omega) (by rw [ea, eb]; exact hab)
    (by rw [el, ea, eb]; exact hl), cov_r hp h ho _ c2, c1⟩

/-- `BitUnpack` of the `len` bytes at `o` of the key, with the bounds `a` and `b`, into the buffer. -/
theorem bu_wp {i o len a b : Nat} (hi : i ≤ n) (ho : o + len ≤ kl) (hl0 : 0 < len)
    (hab : (a, b) ∈ Proof.MlDsa.bitPackParams) (hl : len = 32 * bitlen (a + b)) (ha : a < 2 ^ 31 - 2048)
    (hb : b < 2 ^ 31 - 2048) {t : State} (h : PI kl ol F i σ t) {Q : State → Prop}
    (hQ : ∀ t', PI kl ol F i σ t' → PolyIs t'.mem (pB σ)
      (toRq (bitUnpack (bytesAt σ.mem (pK σ + BitVec.ofNat 64 o) len) a b)) → Q t') :
    WP isa (callAt "vg_mldsa_bit_unpack" Impl.MlDsa.RISCV64.Pack.bitUnpack (buArgs o len a b)) t Q := by
  have := hz.eq; have := hz.lt; have := hp.f3
  have bsub : Region.Sub ⟨pB σ, 1024⟩ ⟨pB σ, 1072⟩ := pre_sub _ (by omega)
  have hg := bu_hg (o := o) (len := len) (by omega) (by omega) ha hb
  have el : (BitVec.ofNat 64 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  have ea : (BitVec.setWidth 32 (BitVec.ofNat 64 a)).toNat = a := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have eb : (BitVec.setWidth 32 (BitVec.ofNat 64 b)).toNat = b := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  obtain ⟨cp, c2, c1⟩ := bu_call hz hp ho hl0 hab hl ha hb h.inv
  refine callV Pack.bitUnpack_verified.1 (by rw [bu_sd]; decide) hg cp c2 c1
    fun t' k hpost => hQ t' (callee_keep hz hi h bu_sd k (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_)) ?_
  · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, bsub⟩
  · rw [List.mem_singleton] at hr; subst hr; exact buf_slots hp
  · rw [List.mem_singleton] at hr; subst hr; exact buf_out hz hp hi
  · have := KeyGen.bu_post hpost
    obtain ⟨e0, e1, e2, e3, e4⟩ := bu_regs hg h.inv (keyR σ o len) (bufW σ)
    rw [e0, e1, e2, e3, e4, el, ea, eb, KeyGen.view_glue_mem, State.withRegions_mem,
      key_keep hp h.inv ho] at this
    exact this

end

/-! ## Pieces: each step, correct and constant time -/

section
variable {kl ol n : Nat} (hz : PSizes kl ol n) {F : State → Nat → Poly}
include hz

theorem ntt_piece {i : Nat} (hi : i < n) {G : State → Poly} :
    Piece (PPre kl ol) PPub (fun σ t => PI kl ol F i σ t ∧ PolyIs t.mem (pB σ) (G σ))
      (fun σ t => PI kl ol F i σ t ∧ PolyIs t.mem (pB σ) (ntt (G σ)))
      (callAt "vg_mldsa_ntt" Impl.MlDsa.RISCV64.Arith.ntt nttArgs) :=
  ⟨fun σ _ hp ⟨h, hb⟩ => ntt_wp hz hp hi h hb fun _ a b => ⟨a, b⟩,
    callV_tr Arith.Ntt.verified.1 Arith.Ntt.verified.2.1 ntt_hg fun x y ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, b₁⟩, ⟨h₂, b₂⟩⟩ => by
      obtain ⟨esp, -, -, eC, eB⟩ := pub
      obtain ⟨a₁, c₁, d₁⟩ := ntt_call p₁ h₁.inv b₁.1
      obtain ⟨a₂, c₂, d₂⟩ := ntt_call p₂ h₂.inv b₂.1
      have e : nttW σ₂ = nttW σ₁ := by simp only [nttW, eB, eC]
      rw [e] at a₂ c₂ d₂
      refine ⟨[], nttW σ₁, a₁, a₂, KeyGen.ip_pub ?_ ?_ ?_, c₁, d₁, c₂, d₂⟩
      · rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, h₁.inv.sp, h₂.inv.sp, esp]
      · rw [(ntt_regs h₁.inv _ _).1, (ntt_regs h₂.inv _ _).1, eB]
      · rw [(ntt_regs h₁.inv _ _).2, (ntt_regs h₂.inv _ _).2, eC]⟩

theorem copyOut_piece {i : Nat} (hi : i < n) {G : State → Poly} (hF : ∀ σ, PPre kl ol σ → F σ i = G σ) :
    Piece (PPre kl ol) PPub (fun σ t => PI kl ol F i σ t ∧ PolyIs t.mem (pB σ) (G σ)) (PI kl ol F (i + 1))
      (copyN (.s11, 0) (.s9, kl + 1024 * i) 1024) :=
  ⟨fun σ _ hp ⟨h, hb⟩ => copyOut_wp hz hp hi h hb (hF σ hp),
    CacheCopy.copyN_tr (by have := hz.eq; have := hz.lt; simp [glueOk, KeyGen.argReg, KeyGen.argOk]; omega)
      fun x y ⟨σ₁, σ₂, _, _, ⟨esp, _, eO, _, eB⟩, ⟨h₁, _⟩, ⟨h₂, _⟩⟩ => by
        obtain ⟨-, g9, -, g11⟩ := regs_of h₁.inv
        obtain ⟨-, k9, -, k11⟩ := regs_of h₂.inv
        exact ⟨by rw [h₁.inv.sp, h₂.inv.sp, esp], by show x.gpr .s11 = y.gpr .s11; rw [g11, k11, eB],
          by show x.gpr .s9 = y.gpr .s9; rw [g9, k9, eO]⟩⟩

theorem t1_piece {i o : Nat} (hi : i ≤ n) (ho : o + 320 ≤ kl) {G : State → Poly}
    (hG : ∀ σ, PPre kl ol σ → G σ = (simpleBitUnpack (bytesAt σ.mem (pK σ + BitVec.ofNat 64 o) 320) t1Max).map
      fun c => ofInt (c * 2 ^ d : Nat)) :
    Piece (PPre kl ol) PPub (PI kl ol F i) (fun σ t => PI kl ol F i σ t ∧ PolyIs t.mem (pB σ) (G σ))
      (callAt "vg_mldsa_unpack_t1" Impl.MlDsa.RISCV64.Pack.unpackT1 (t1Args o)) := by
  have := hz.eq; have := hz.lt
  have hO : o < 2 ^ 31 - 2048 := by omega
  exact ⟨fun σ _ hp h => t1_wp hz hp hi ho h fun _ a b => ⟨a, by rw [hG σ hp]; exact b⟩,
    callV_tr Pack.unpackT1_verified.1 Pack.unpackT1_verified.2.1 (t1_hg hO)
      fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => by
        obtain ⟨esp, eK, -, -, eB⟩ := pub
        obtain ⟨a₁, c₁, d₁⟩ := t1_call hz p₁ ho h₁.inv
        obtain ⟨a₂, c₂, d₂⟩ := t1_call hz p₂ ho h₂.inv
        have e1 : keyR σ₂ o 320 = keyR σ₁ o 320 := by simp only [keyR, eK]
        have e2 : bufW σ₂ = bufW σ₁ := by simp only [bufW, eB]
        rw [e1, e2] at a₂ c₂
        rw [e2] at d₂
        refine ⟨_, _, a₁, a₂, KeyGen.t1_pub ?_ ?_ ?_, c₁, d₁, c₂, d₂⟩
        · rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, h₁.inv.sp, h₂.inv.sp, esp]
        · rw [(t1_regs hO h₁.inv _ _).1, (t1_regs hO h₂.inv _ _).1, eK]
        · rw [(t1_regs hO h₁.inv _ _).2, (t1_regs hO h₂.inv _ _).2, eB]⟩

theorem bu_piece {i o len a b : Nat} (hi : i ≤ n) (ho : o + len ≤ kl) (hl0 : 0 < len)
    (hab : (a, b) ∈ Proof.MlDsa.bitPackParams) (hl : len = 32 * bitlen (a + b)) (ha : a < 2 ^ 31 - 2048)
    (hb : b < 2 ^ 31 - 2048) {G : State → Poly}
    (hG : ∀ σ, PPre kl ol σ → G σ = toRq (bitUnpack (bytesAt σ.mem (pK σ + BitVec.ofNat 64 o) len) a b)) :
    Piece (PPre kl ol) PPub (PI kl ol F i) (fun σ t => PI kl ol F i σ t ∧ PolyIs t.mem (pB σ) (G σ))
      (callAt "vg_mldsa_bit_unpack" Impl.MlDsa.RISCV64.Pack.bitUnpack (buArgs o len a b)) := by
  have := hz.eq; have := hz.lt
  have hg := bu_hg (o := o) (len := len) (by omega) (by omega) ha hb
  exact ⟨fun σ _ hp h => bu_wp hz hp hi ho hl0 hab hl ha hb h fun _ x y => ⟨x, by rw [hG σ hp]; exact y⟩,
    callV_tr Pack.bitUnpack_verified.1 Pack.bitUnpack_verified.2.1 hg
      fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => by
        obtain ⟨esp, eK, -, -, eB⟩ := pub
        obtain ⟨a₁, c₁, d₁⟩ := bu_call hz p₁ ho hl0 hab hl ha hb h₁.inv
        obtain ⟨a₂, c₂, d₂⟩ := bu_call hz p₂ ho hl0 hab hl ha hb h₂.inv
        have e1 : keyR σ₂ o len = keyR σ₁ o len := by simp only [keyR, eK]
        have e2 : bufW σ₂ = bufW σ₁ := by simp only [bufW, eB]
        rw [e1, e2] at a₂ c₂
        rw [e2] at d₂
        obtain ⟨u0, u1, u2, u3, u4⟩ := bu_regs hg h₁.inv (keyR σ₁ o len) (bufW σ₁)
        obtain ⟨v0, v1, v2, v3, v4⟩ := bu_regs hg h₂.inv (keyR σ₁ o len) (bufW σ₁)
        refine ⟨_, _, a₁, a₂, KeyGen.bu_pub ?_ ?_ ?_ ?_ ?_ ?_, c₁, d₁, c₂, d₂⟩
        · rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, h₁.inv.sp, h₂.inv.sp, esp]
        · rw [u0, v0, eK]
        · rw [u1, v1]
        · rw [u2, v2]
        · rw [u3, v3]
        · rw [u4, v4, eB]⟩

end

/-! ## The body -/

/-- After the body: our caller's registers, the key copied and the polynomials after it. -/
def PDone (kl n : Nat) (F : State → Nat → Poly) (σ t : State) : Prop :=
  abiPreserved σ t ∧ bytesAt t.mem (pO σ) kl = bytesAt σ.mem (pK σ) kl ∧
    ∀ j < n, PolyIs t.mem (pO σ + BitVec.ofNat 64 (kl + 1024 * j)) (F σ j)

section
variable {kl ol n : Nat} (hz : PSizes kl ol n) {F : State → Nat → Poly}
include hz

omit hz in
theorem setup_piece : Piece (PPre kl ol) PPub (fun σ s => s = σ) (fun σ => PS ol σ) (.block prepEnter) :=
  ⟨fun σ s hp hs => by subst hs; exact setup_wp hp,
    Proof.MlKem.RISCV64.Sample.taint_block [.a0, .a1, .a2, .a3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂; exact pub.1)
      (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
        subst h₁ h₂
        obtain ⟨-, e0, e1, e2, e3⟩ := pub
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [e0, e1, e2, e3]) (by taint_decide)⟩

theorem keyCopy_piece (hk : 0 < kl) :
    Piece (PPre kl ol) PPub (fun σ => PS ol σ) (PI kl ol F 0) (copyN (.s10, 0) (.s9, 0) kl) :=
  ⟨fun σ _ hp h => keyCopy_wp hz hp hk h,
    CacheCopy.copyN_tr (copy_glue (by have := hz.eq; have := hz.lt; omega))
      fun x y ⟨σ₁, σ₂, _, _, ⟨esp, eK, eO, _, _⟩, h₁, h₂⟩ => by
        obtain ⟨-, g9, g10, -⟩ := regs_of h₁
        obtain ⟨-, k9, k10, -⟩ := regs_of h₂
        exact ⟨by rw [h₁.sp, h₂.sp, esp], by show x.gpr .s10 = y.gpr .s10; rw [g10, k10, eK],
          by show x.gpr .s9 = y.gpr .s9; rw [g9, k9, eO]⟩⟩

omit hz in
theorem restore_piece :
    Piece (PPre kl ol) PPub (PI kl ol F n) (PDone kl n F) (.block (restoreRegs .s11 oSV keptRegs)) :=
  ⟨fun σ t hp h => by
    have := hp.f3
    obtain ⟨-, -, -, g11⟩ := regs_of h.inv
    refine restore_ok h.inv hp.al3 g11 (by decide) (by decide) (by decide) (by decide)
      (fun q hq => ?_) fun t' g sp lr m _ => ⟨⟨g, sp, lr⟩, by rw [m]; exact h.out, fun j hj => by
        rw [m]; exact h.polys j hj⟩
    have h1 : q.2 + 8 ≤ 1064 := by
      have := (Proof.Ed25519.RISCV64.Whole.slots_in oSV keptRegs q (by
        revert q; decide))
      simpa [oSV, keptRegs] using this.2
    exact ⟨⟨pB σ, 1072⟩, by rw [h.inv.rd, h.inv.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩,
    Proof.MlKem.RISCV64.Sample.taint_block [.s11] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
        rw [h₁.inv.sp, h₂.inv.sp]; exact pub.1)
      (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
        rw [List.mem_singleton] at hr; subst hr
        rw [(regs_of h₁.inv).2.2.2, (regs_of h₂.inv).2.2.2]; exact pub.2.2.2.2) (by taint_decide)⟩

/-- The body, from the polynomials' pieces. -/
theorem body_piece (hk : 0 < kl) {poly : Nat → Prog isa}
    (hs : ∀ i < n, Piece (PPre kl ol) PPub (PI kl ol F i) (PI kl ol F (i + 1)) (poly i)) :
    Piece (PPre kl ol) PPub (fun σ s => s = σ) (PDone kl n F) (prepBody kl n poly) := by
  have h := KeyGen.Piece.seqR (Pre := PPre kl ol) (Pub := PPub) (I := fun i => PI kl ol F i) (f := poly) n 0
    fun i _ hi => hs i (by omega)
  rw [Nat.zero_add] at h
  exact setup_piece.seq ((keyCopy_piece hz hk).seq (h.seq restore_piece))

end

/-! ## The keys -/

/-- The sizes and bounds of a parameter set. -/
structure PFacts (p : Params) : Prop where
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = 128 + secretLen p * (p.ℓ + p.k) + 416 * p.k
  ppk : preparedPublicKeyBytes p = p.pkLen + 1024 * p.k
  psk : preparedSecretKeyBytes p = p.skLen + 1024 * (p.ℓ + 2 * p.k)
  ppk_lt : preparedPublicKeyBytes p < 2 ^ 31 - 2048
  psk_lt : preparedSecretKeyBytes p < 2 ^ 31 - 2048
  eta : (p.η, p.η) ∈ Proof.MlDsa.bitPackParams
  sl : secretLen p = 32 * bitlen (p.η + p.η)
  sl0 : 0 < secretLen p
  eta_lt : p.η < 2 ^ 31 - 2048

theorem pfacts {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : PFacts p := by
  rcases hp3 with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- The public key's polynomials. -/
def FPub (p : Params) (σ : State) (i : Nat) : Poly :=
  (preparedPublicPolys p (bytesAt σ.mem (pK σ) p.pkLen))[i]!

/-- The private key's polynomials. -/
def FSec (p : Params) (σ : State) (i : Nat) : Poly :=
  (preparedSecretPolys p (bytesAt σ.mem (pK σ) p.skLen))[i]!

section
variable {p : Params} (hF : PFacts p)
include hF

theorem public_sizes : PSizes p.pkLen (preparedPublicKeyBytes p) p.k := ⟨hF.ppk, hF.ppk_lt⟩

theorem secret_sizes : PSizes p.skLen (preparedSecretKeyBytes p) (p.ℓ + 2 * p.k) := ⟨hF.psk, hF.psk_lt⟩

theorem public_piece {i : Nat} (hi : i < p.k) :
    Piece (PPre p.pkLen (preparedPublicKeyBytes p)) PPub (PI p.pkLen (preparedPublicKeyBytes p) (FPub p) i)
      (PI p.pkLen (preparedPublicKeyBytes p) (FPub p) (i + 1)) (publicPoly p i) := by
  have hz := public_sizes hF
  have ho : 32 + 320 * i + 320 ≤ p.pkLen := by rw [hF.pk]; omega
  unfold publicPoly nttOut
  refine (t1_piece hz (Nat.le_of_lt hi) ho (fun _ _ => rfl)).seq ((ntt_piece hz hi).seq
    (copyOut_piece hz hi fun σ _ => ?_))
  unfold FPub
  rw [Proof.MlDsa.PreparedKey.public_poly _ _ hi]
  unfold Proof.MlDsa.Verify.t1Hat Proof.MlDsa.Verify.vT1
  rw [Proof.MlKem.bytesAt_slice _ _ ho]

omit hF in
/-- Polynomial `i` of `s₁ ‖ s₂ ‖ t₀`, decoded from its piece of a private key. -/
theorem secret_value (key : List Byte) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    ntt (toRq (bitUnpack ((key.drop (secretPiece p i).1).take (secretPiece p i).2.1) (secretPiece p i).2.2.1
      (secretPiece p i).2.2.2)) = (preparedSecretPolys p key)[i]! := by
  have hlen : secretLen p = Proof.MlDsa.Sign.lenS p := rfl
  by_cases h1 : i < p.ℓ
  · rw [Proof.MlDsa.PreparedKey.secret_s1 p key h1]
    simp only [secretPiece, ite_eq_left (show i < p.ℓ + p.k by omega), hlen]
    rfl
  · by_cases h2 : i < p.ℓ + p.k
    · have hj : i - p.ℓ < p.k := by omega
      have he : p.ℓ + (i - p.ℓ) = i := by omega
      rw [← he, Proof.MlDsa.PreparedKey.secret_s2 p key hj]
      simp only [secretPiece, ite_eq_left (show p.ℓ + (i - p.ℓ) < p.ℓ + p.k by omega), hlen]
      unfold Proof.MlDsa.Sign.s2F
      rw [Nat.mul_add]
      congr 5 <;> omega
    · have hj : i - (p.ℓ + p.k) < p.k := by omega
      have he : p.ℓ + p.k + (i - (p.ℓ + p.k)) = i := by omega
      rw [← he, Proof.MlDsa.PreparedKey.secret_t0 p key hj]
      simp only [secretPiece, ite_eq_right (show ¬ p.ℓ + p.k + (i - (p.ℓ + p.k)) < p.ℓ + p.k by omega), hlen]
      unfold Proof.MlDsa.Sign.t0F
      have hoff : 128 + Proof.MlDsa.Sign.lenS p * (p.ℓ + p.k) +
          416 * (p.ℓ + p.k + (i - (p.ℓ + p.k)) - p.ℓ - p.k) =
          128 + Proof.MlDsa.Sign.lenS p * p.ℓ + Proof.MlDsa.Sign.lenS p * p.k +
            32 * d * (i - (p.ℓ + p.k)) := by
        rw [Nat.mul_add]
        simp only [d]
        omega
      rw [hoff]
      rfl

/-- The bounds of a private key's piece. -/
theorem secretPiece_ok {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    (secretPiece p i).1 + (secretPiece p i).2.1 ≤ p.skLen ∧ 0 < (secretPiece p i).2.1 ∧
      ((secretPiece p i).2.2.1, (secretPiece p i).2.2.2) ∈ Proof.MlDsa.bitPackParams ∧
      (secretPiece p i).2.1 = 32 * bitlen ((secretPiece p i).2.2.1 + (secretPiece p i).2.2.2) ∧
      (secretPiece p i).2.2.1 < 2 ^ 31 - 2048 ∧ (secretPiece p i).2.2.2 < 2 ^ 31 - 2048 := by
  unfold secretPiece
  split
  · dsimp only
    have := Nat.mul_le_mul_left (secretLen p) (show i + 1 ≤ p.ℓ + p.k by omega)
    rw [Nat.mul_succ] at this
    exact ⟨by rw [hF.sk]; omega, hF.sl0, hF.eta, hF.sl, hF.eta_lt, hF.eta_lt⟩
  · dsimp only
    exact ⟨by rw [hF.sk]; omega, by decide, by decide, by decide, by decide, by decide⟩

theorem secret_piece {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    Piece (PPre p.skLen (preparedSecretKeyBytes p)) PPub (PI p.skLen (preparedSecretKeyBytes p) (FSec p) i)
      (PI p.skLen (preparedSecretKeyBytes p) (FSec p) (i + 1)) (secretPoly p i) := by
  have hz := secret_sizes hF
  obtain ⟨ho, hl0, hab, hl, ha, hb⟩ := secretPiece_ok hF hi
  unfold secretPoly nttOut
  refine (bu_piece hz (Nat.le_of_lt hi) ho hl0 hab hl ha hb (fun _ _ => rfl)).seq ((ntt_piece hz hi).seq
    (copyOut_piece hz hi fun σ _ => ?_))
  unfold FSec
  rw [← secret_value _ hi, Proof.MlKem.bytesAt_slice _ _ ho]

end

/-! ## The contracts -/

/-- The postconditions of the prepare functions. -/
def publicPost (p : Params) : (preparePublicKeySig p).Post RISCV64.abi.ptrBits :=
  fun pk prepared _scratch m m' _ =>
    bytesAt m' prepared p.pkLen = bytesAt m pk p.pkLen ∧ PreparedPublicKey p m' prepared

def secretPost (p : Params) : (prepareSecretKeySig p).Post RISCV64.abi.ptrBits :=
  fun sk prepared _scratch m m' _ =>
    bytesAt m' prepared p.skLen = bytesAt m sk p.skLen ∧ PreparedSecretKey p m' prepared

/-- `vg_mldsa*_prepare_verifying_key` with its buffer as a last argument. -/
def publicScratchSig (p : Params) : Sig where
  params := (preparePublicKeySig p).params ++ [("work", .array true .u64 bufWords)]

def publicScratchContract (p : Params) (stack : Nat := 0) : Contract isa :=
  (publicScratchSig p).contract RISCV64.abi
    (post := fun pk prepared scratch _work => publicPost p pk prepared scratch)
    (writeArgs := true) (stack := stack)

theorem publicScratchContract_eq (p : Params) (stack : Nat) :
    publicScratchContract p stack = Sig.scratchContract RISCV64.abi (preparePublicKeySig p) "work" .u64 bufWords
      (Curry.const (fun _ => True) _) (publicPost p) true stack := rfl

/-- `vg_mldsa*_prepare_signing_key` with its buffer as a last argument. -/
def secretScratchSig (p : Params) : Sig where
  params := (prepareSecretKeySig p).params ++ [("work", .array true .u64 bufWords)]

def secretScratchContract (p : Params) (stack : Nat := 0) : Contract isa :=
  (secretScratchSig p).contract RISCV64.abi
    (post := fun sk prepared scratch _work => secretPost p sk prepared scratch)
    (writeArgs := true) (stack := stack)

theorem secretScratchContract_eq (p : Params) (stack : Nat) :
    secretScratchContract p stack = Sig.scratchContract RISCV64.abi (prepareSecretKeySig p) "work" .u64 bufWords
      (Curry.const (fun _ => True) _) (secretPost p) true stack := rfl

theorem public_pre {p : Params} {s : State} (h : (publicScratchContract p).pre s) :
    PPre p.pkLen (preparedPublicKeyBytes p) s := by
  sig_pre [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs] at h
  rw [show bufWords * 8 = 1072 from rfl] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem secret_pre {p : Params} {s : State} (h : (secretScratchContract p).pre s) :
    PPre p.skLen (preparedSecretKeyBytes p) s := by
  sig_pre [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs] at h
  rw [show bufWords * 8 = 1072 from rfl] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem public_pub {p : Params} {s₁ s₂ : State} (h : (publicScratchContract p).pub s₁ s₂) : PPub s₁ s₂ := by
  sig_pub [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs] at h
  exact h

theorem secret_pub {p : Params} {s₁ s₂ : State} (h : (secretScratchContract p).pub s₁ s₂) : PPub s₁ s₂ := by
  sig_pub [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs] at h
  exact h

theorem publicPost_out {p : Params} (hF : PFacts p) : ∀ vs m m₁ m₂ r,
    vs.length = ((preparePublicKeySig p).words RISCV64.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs (preparePublicKeySig p).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((preparePublicKeySig p).words RISCV64.abi.ptrBits) (publicPost p) vs m m₁ r →
      Curry.apply ((preparePublicKeySig p).words RISCV64.abi.ptrBits) (publicPost p) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨pr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [preparePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hlt := hF.ppk_lt
  have hs : ∀ k < p.pkLen + 1024 * p.k, m₂ (pr + BitVec.ofNat 64 k) = m₁ (pr + BitVec.ofNat 64 k) :=
    fun k hk => (hb.2.1 _ (Offset.contains_base _ (by simp only [Elem.size]; rw [hF.ppk] at hlt ⊢; omega)
      (by rw [hF.ppk] at hlt; omega))).symm
  obtain ⟨h1, h2⟩ := h
  have e : ArgWord.addr.ofRaw pr = pr := rfl
  rw [e] at h1 h2
  show bytesAt m₂ pr p.pkLen = bytesAt m (ArgWord.addr.ofRaw pk) p.pkLen ∧ PreparedPublicKey p m₂ pr
  have hk : bytesAt m₂ pr p.pkLen = bytesAt m₁ pr p.pkLen :=
    Proof.MlKem.bytesAt_congr fun i hi => hs i (by omega)
  refine ⟨hk.trans h1, ?_⟩
  rw [Proof.MlDsa.preparedPublicKey_iff] at h2 ⊢
  rw [hk]
  exact polys_congr hs h2

theorem secretPost_out {p : Params} (hF : PFacts p) : ∀ vs m m₁ m₂ r,
    vs.length = ((prepareSecretKeySig p).words RISCV64.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs (prepareSecretKeySig p).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((prepareSecretKeySig p).words RISCV64.abi.ptrBits) (secretPost p) vs m m₁ r →
      Curry.apply ((prepareSecretKeySig p).words RISCV64.abi.ptrBits) (secretPost p) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨pr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [prepareSecretKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hlt := hF.psk_lt
  have hs : ∀ k < p.skLen + 1024 * (p.ℓ + 2 * p.k), m₂ (pr + BitVec.ofNat 64 k) = m₁ (pr + BitVec.ofNat 64 k) :=
    fun k hk => (hb.2.1 _ (Offset.contains_base _ (by simp only [Elem.size]; rw [hF.psk] at hlt ⊢; omega)
      (by rw [hF.psk] at hlt; omega))).symm
  obtain ⟨h1, h2⟩ := h
  have e : ArgWord.addr.ofRaw pr = pr := rfl
  rw [e] at h1 h2
  show bytesAt m₂ pr p.skLen = bytesAt m (ArgWord.addr.ofRaw pk) p.skLen ∧ PreparedSecretKey p m₂ pr
  have hk : bytesAt m₂ pr p.skLen = bytesAt m₁ pr p.skLen :=
    Proof.MlKem.bytesAt_congr fun i hi => hs i (by omega)
  refine ⟨hk.trans h1, ?_⟩
  rw [Proof.MlDsa.preparedSecretKey_iff] at h2 ⊢
  rw [hk]
  exact polys_congr hs h2

/-- The polynomials after the key, as the spec states them. -/
theorem polys_spec {m : Mem} {key : Addr} {kl N : Nat} {F : Nat → Poly}
    (h : ∀ j < N, PolyIs m (key + BitVec.ofNat 64 (kl + 1024 * j)) (F j)) :
    ∀ j < N, PolyIs m (key + BitVec.ofNat 64 (kl + 4 * VG.Spec.MlDsa.n * j)) (F j) := fun j hj => by
  rw [show 4 * VG.Spec.MlDsa.n * j = 1024 * j by simp only [VG.Spec.MlDsa.n]]
  exact h j hj

section
variable {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
include hp3

/-- The body of `vg_mldsa*_prepare_verifying_key`, with its buffer as an argument. -/
theorem publicBody_verified (hsat : ∃ s, (publicScratchContract p).pre s) :
    Verified RISCV64.target (prepBody p.pkLen p.k (publicPoly p)) (publicScratchContract p) := by
  have hF := pfacts hp3
  have hb := body_piece (public_sizes hF) (by rw [hF.pk]; omega) fun i hi => public_piece hF hi
  refine ⟨fun s hs => WP.mono (hb.ok s s (public_pre hs) rfl) fun t ⟨ha, hout, hpolys⟩ => ⟨ha, ?_⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ =>
      KeyGen.relStart hb.tr s₁ s₂ t₁ t₂ s₁' s₂' (public_pre h₁) (public_pre h₂) (public_pub hpub) e₁ e₂, hsat⟩
  sig_post [publicScratchContract, publicScratchSig, preparePublicKeySig, publicPost, RISCV64.abi, RISCV64.argRegs]
  refine ⟨hout, ?_⟩
  rw [Proof.MlDsa.preparedPublicKey_iff, hout]
  exact polys_spec hpolys

/-- The body of `vg_mldsa*_prepare_signing_key`, with its buffer as an argument. -/
theorem secretBody_verified (hsat : ∃ s, (secretScratchContract p).pre s) :
    Verified RISCV64.target (prepBody p.skLen (p.ℓ + 2 * p.k) (secretPoly p)) (secretScratchContract p) := by
  have hF := pfacts hp3
  have hb := body_piece (secret_sizes hF) (by rw [hF.sk]; omega) fun i hi => secret_piece hF hi
  refine ⟨fun s hs => WP.mono (hb.ok s s (secret_pre hs) rfl) fun t ⟨ha, hout, hpolys⟩ => ⟨ha, ?_⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ =>
      KeyGen.relStart hb.tr s₁ s₂ t₁ t₂ s₁' s₂' (secret_pre h₁) (secret_pre h₂) (secret_pub hpub) e₁ e₂, hsat⟩
  sig_post [secretScratchContract, secretScratchSig, prepareSecretKeySig, secretPost, RISCV64.abi, RISCV64.argRegs]
  refine ⟨hout, ?_⟩
  rw [Proof.MlDsa.preparedSecretKey_iff, hout]
  exact polys_spec hpolys

/-- `vg_mldsa*_prepare_verifying_key`, with its buffer in a frame of 1072 bytes on the stack. -/
theorem preparePublic_verified (hsat : ∃ s, (publicScratchContract p).pre s)
    (hsat' : ∃ s, (preparePublicKeyContract p RISCV64.abi 1072).pre s) :
    Verified RISCV64.target (preparePublic p) (preparePublicKeyContract p RISCV64.abi 1072) :=
  RISCV64.Verified.stackScratchWiped (sig := preparePublicKeySig p) (nm := "work") (e := .u64) (n := bufWords)
    (post := publicPost p) (wa := true) (stack := 0) (bytes := bufBytes) (words := bufWords)
    (publicScratchContract_eq p 0 ▸ publicBody_verified hp3 hsat)
    (by rw [show ((preparePublicKeySig p).words RISCV64.abi.ptrBits).length = 3 from rfl]; decide) (by decide) (by decide)
    (publicPost_out (pfacts hp3)) hsat' rfl

/-- `vg_mldsa*_prepare_signing_key`, with its buffer in a frame of 1072 bytes on the stack. -/
theorem prepareSecret_verified (hsat : ∃ s, (secretScratchContract p).pre s)
    (hsat' : ∃ s, (prepareSecretKeyContract p RISCV64.abi 1072).pre s) :
    Verified RISCV64.target (prepareSecret p) (prepareSecretKeyContract p RISCV64.abi 1072) :=
  RISCV64.Verified.stackScratchWiped (sig := prepareSecretKeySig p) (nm := "work") (e := .u64) (n := bufWords)
    (post := secretPost p) (wa := true) (stack := 0) (bytes := bufBytes) (words := bufWords)
    (secretScratchContract_eq p 0 ▸ secretBody_verified hp3 hsat)
    (by rw [show ((prepareSecretKeySig p).words RISCV64.abi.ptrBits).length = 3 from rfl]; decide) (by decide) (by decide)
    (secretPost_out (pfacts hp3)) hsat' rfl

end

end VG.Proof.MlDsa.RISCV64.PreparedKey
