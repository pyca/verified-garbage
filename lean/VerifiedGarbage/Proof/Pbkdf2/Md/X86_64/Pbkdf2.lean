module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Pbkdf2.Md.X86_64.PbkCommon`, which only this module used -/

section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s parts

The precondition of `pbkdf2` (`Pre`), the parts of its `scratch`, what every
piece of it keeps (`KR`), and the calls of the functions it calls: the hash
function's streaming functions (`VG.Proof.Pbkdf2.Md.X86_64.Calls.StreamOK`), HMAC's
`init` and `finalize`, and `iterate`, whose proofs it takes as hypotheses.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Sizes pbkG)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs ne_rsp callEntry_bytes SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .rdi
abbrev pwl : Nat := (s₀.gpr .rsi).toNat
abbrev salt : Addr := s₀.gpr .rdx
abbrev sl : Nat := (s₀.gpr .rcx).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .r8).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .r9
abbrev ol : Nat := (stackArg s₀ 0).toNat
abbrev scr : Addr := stackArg s₀ 1
abbrev pwR : Region := ⟨pw s₀, pwl s₀⟩
abbrev saltR : Region := ⟨salt s₀, sl s₀⟩
abbrev outR : Region := ⟨out s₀, ol s₀⟩
abbrev scR : Region := ⟨scr s₀, (H.W + H.S) * 8⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := ⟨s₀.gpr .rsp - BitVec.ofNat 64 24, 24⟩
/-- An address in `scratch`, and a part of it. -/
abbrev A (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- Our caller's registers, `out` and `c - 1`. -/
abbrev hdrR : Region := sR s₀ H.sv 64
/-- The working space of the functions we call. -/
abbrev lowR : Region := ⟨scr s₀, 8 * H.W⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  sp₁ : 24 ≤ (s₀.gpr .rsp).toNat
  sp₂ : (s₀.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s₀.rd = [pwR s₀, saltR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scR (H := H) s₀]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR (H := H) s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR (H := H) s₀)
  o_s : (outR s₀).Disjoint (scR (H := H) s₀)
  o_a : (outR s₀).Disjoint (argR s₀)
  s_a : (scR (H := H) s₀).Disjoint (argR s₀)
  ret_pw : (retR s₀).Disjoint (pwR s₀)
  ret_sa : (retR s₀).Disjoint (saltR s₀)
  ret_o : (retR s₀).Disjoint (outR s₀)
  ret_s : (retR s₀).Disjoint (scR (H := H) s₀)
  ret_a : (retR s₀).Disjoint (argR s₀)
  stk_pw : (stkR s₀).Disjoint (pwR s₀)
  stk_sa : (stkR s₀).Disjoint (saltR s₀)
  stk_o : (stkR s₀).Disjoint (outR s₀)
  stk_s : (stkR s₀).Disjoint (scR (H := H) s₀)
  stk_a : (stkR s₀).Disjoint (argR s₀)
  pwnw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 64
  sanw : (salt s₀).toNat + sl s₀ ≤ 2 ^ 64
  onw : (out s₀).toNat + ol s₀ ≤ 2 ^ 64
  snw : (scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * H.D

theorem pre_of (hH : HashOK H) {s₀ : State} (h : (pbkG hH.SH (H.W + H.S)).pre s₀) : Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  have hD := hH.hD
  simp only [hD] at h26
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

/-- The sizes, as facts about natural numbers. -/
structure PSizes (H : Hash) : Prop where
  z : Sizes H
  W : H.W ≤ 256

theorem _root_.VG.Proof.Pbkdf2.Md.X86_64.HashOK.psizes (hH : HashOK H) : PSizes H := ⟨hH.sizes, hH.hW⟩

/-! ## The parts of `scratch` -/

/-- Where the parts of `scratch` are. -/
theorem layout : H.sv = 8 * H.W ∧ H.outO = 8 * H.W + 48 ∧ H.cO = 8 * H.W + 56 ∧ H.st0O = 8 * H.W + 64 ∧
    H.st1O = 8 * H.W + 64 + H.S ∧ H.stSO = 8 * H.W + 64 + 2 * H.S ∧ H.stWO = 8 * H.W + 64 + 3 * H.S ∧
    H.uO = 8 * H.W + 64 + 4 * H.S ∧ H.tO = 8 * H.W + 64 + 4 * H.S + H.D ∧
    H.hkO = 8 * H.W + 64 + 4 * H.S + 2 * H.D ∧ H.intO = 8 * H.W + 64 + 4 * H.S + 2 * H.D + H.P.N ∧
    H.S = H.P.N + H.P.B := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [Hash.sv, Hash.st0O, Hash.st1O, Hash.stSO, Hash.stWO, Hash.uO, Hash.tO,
      Hash.hkO, Hash.intO] <;> omega_using []

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)

include hz in
/-- The parts of `scratch`, as offsets: they end before its end. -/
theorem end_le : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  have := hz.z.N; have := hz.z.D; have := hz.z.B; have := layout (H := H)
  omega_arith

include hz in
theorem L_lt : (H.W + H.S) * 8 < 2 ^ 64 := by
  have := hz.W; have := hz.z.N; have := hz.z.B_le; show (H.W + (H.P.N + H.P.B)) * 8 < 2 ^ 64; omega_arith

theorem part_sub {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) : Region.Sub (sR s₀ o n) (scR (H := H) s₀) :=
  Offset.sub_base _ h

include hz in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ (H.W + H.S) * 8)
    (hb : b + n ≤ (H.W + H.S) * 8) : Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := L_lt hz; exact Offset.disjoint _ h (by omega_using [ha, this]) (by omega_using [hb, this])

include hz in
theorem low_disj {b n : Nat} (hb : 8 * H.W ≤ b) (hbn : b + n ≤ (H.W + H.S) * 8) :
    Region.Disjoint (sR s₀ b n) (lowR (H := H) s₀) := by
  have := L_lt hz; exact Offset.disjoint_base _ hb (by omega_using [hbn, this])

theorem low_sub : Region.Sub (lowR (H := H) s₀) (scR (H := H) s₀) :=
  Region.sub_prefix (by show 8 * H.W ≤ (H.W + H.S) * 8; omega_using [])

include hp hz in
theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) :
    InRegions s.wr (A s₀ o) n := by
  have := L_lt hz
  exact ⟨scR (H := H) s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ h (by omega_using [h, this])⟩

include hp in
theorem sc_mem : scR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  fun x h₁ h₂ => Offset.base_disjoint_below (s₀.gpr .rsp) (n := 24) (k := 8) (by omega_using []) x h₂ h₁

/-- The 8 · (depth + 1) bytes below `rsp` that a call of depth at most 2 uses. -/
theorem below_stk {n : Nat} (hn : n ≤ 24) : Region.Sub (below (s₀.gpr .rsp) n) (stkR s₀) :=
  below_sub hn (by omega_using [])

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's registers,
`out` and `c - 1` in `scratch`, and everything written is in `out`,
`scratch` or the stack. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.hh (scr s₀) s₀ s.mem
  outW : s.mem.readW (A s₀ H.outO) 64 = out s₀
  cW : s.mem.readW (A s₀ H.cO) 64 = BitVec.ofNat 64 (cc s₀ - 1)
  frame : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s.mem

/-- Registers `KR` fixes. -/
abbrev kregs : List Reg := [.r15, .rsp]

theorem hdr_sub {s₀ : State} {o : Nat} (h₁ : H.sv ≤ o) (h₂ : o + 8 ≤ H.sv + 64) :
    Region.Sub ⟨A s₀ o, 8⟩ (hdrR (H := H) s₀) := Offset.sub _ h₁ h₂

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (hdrR (H := H) s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [outR s₀, scR (H := H) s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) s₀ s' := by
  have hs : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H.hh (scr s₀)) (hdrR (H := H) s₀) := Offset.sub _ (Nat.le_refl _) (by
    show 8 * H.W + 48 ≤ 8 * H.W + 64; omega_using [])
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.rsp, h15.trans h.r15,
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left hs, ?_, ?_, h.frame.trans (hf.sub hsub)⟩
  · rw [← h.outW]
    exact hf.readW (r := ⟨A s₀ H.outO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.outO]) (by simp [Hash.outO])))
      (by decide)
  · rw [← h.cW]
    exact hf.readW (r := ⟨A s₀ H.cO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.cO]) (by simp [Hash.cO])))
      (by decide)

omit hp in
/-- A write into a part of `scratch` after its header keeps `KR`. -/
theorem KR.write {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {o n : Nat}
    (ho : H.st0O ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by simpa [Hash.st0O] using ho)) (by
        have := end_le hz; simp only [Hash.st0O] at ho; omega_using [ho, hon]) hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after its header, or its
working space, and the stack below `rsp`. -/
theorem KR.call {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    KR (H := H) s₀ s' := by
  have := end_le hz; have := layout (H := H)
  have hst : H.sv + 64 = H.st0O := by simp [Hash.st0O]
  refine h.keep hrd hwr (hcs _ (by simp [calleeSaved])) (hcs _ (by simp [calleeSaved])) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (low_disj hz (Nat.le_refl _) (by omega_arith)).sub_right (Region.sub_prefix hk)
      · exact part_disj hz (Or.inl (by rw [hst]; exact h₁)) (by rw [hst]; omega_using [h₁, h₂]) h₂
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ((hp.stk_s.sub_left (below_stk hn)).sub_right (part_sub (by rw [hst]; omega_arith))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega_using [hk])⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ⟨_, by simp, below_stk hn⟩

omit hp hz in
/-- The regions only read are the same as on entry. -/
theorem KR.bytes {s : State} (h : KR (H := H) s₀ s) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ [outR s₀, scR (H := H) s₀, stkR s₀], Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep h.frame hd hn

omit hz in
theorem KR.pwBytes {s : State} (h : KR (H := H) s₀ s) :
    bytesAt s.mem (pw s₀) (pwl s₀) = bytesAt s₀.mem (pw s₀) (pwl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.stk_pw.symm) (by have := hp.pwnw; omega_using [this])

omit hz in
theorem KR.saltBytes {s : State} (h : KR (H := H) s₀ s) :
    bytesAt s.mem (salt s₀) (sl s₀) = bytesAt s₀.mem (salt s₀) (sl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.stk_sa.symm) (by have := hp.sanw; omega_using [this])

omit hp hz in
theorem KR.readW {s : State} (h : KR (H := H) s₀ s) {R : Region} {a : Addr} (hc : R.Contains a 8)
    (hd : ∀ r ∈ [outR s₀, scR (H := H) s₀, stkR s₀], R.Disjoint r) :
    s.mem.readW a 64 = s₀.mem.readW a 64 :=
  h.frame.readW hc hd (by decide)

omit hz in
theorem KR.ret {s : State} (h : KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
  h.readW (R := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s
    · exact stk_ret.symm)

omit hz in
/-- `out_len`, on the stack. -/
theorem KR.olW {s : State} (h : KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s₀ 0 :=
  h.readW (R := argR s₀) (contains_pre (by decide)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.stk_a.symm)

end

/-! ## Facts about the offsets

Each proved once, by `omega` on `layout`, for the step proofs: an `omega`
over a step's context, which holds many facts about states and sizes, costs
far more. -/

theorem PSizes.B_ge (hz : PSizes H) : 64 ≤ H.P.B := by rcases hz.z.B with h | h <;> omega_using [h]
theorem PSizes.o_0_lt_S (hz : PSizes H) : 0 < H.S := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_B_1_lt_p31 (hz : PSizes H) : H.P.B + 1 < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_1_lt_p64 (hz : PSizes H) : H.P.B + 1 < 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_4_lt_p31 (hz : PSizes H) : H.P.B + 4 < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_lt_p31 (hz : PSizes H) : H.P.B < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_lt_p32 (hz : PSizes H) : H.P.B < 2 ^ 32 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_le_p64 (hz : PSizes H) : H.D ≤ 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_p31 (hz : PSizes H) : H.D < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_p32 (hz : PSizes H) : H.D < 2 ^ 32 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_p64 (hz : PSizes H) : H.D < 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_S_lt_p31 (hz : PSizes H) : H.S < 2 ^ 31 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_W8_48_le_L (hz : PSizes H) : 8 * H.W + 48 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_W8_48_le_outO (hz : PSizes H) : 8 * H.W + 48 ≤ H.outO := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_L (hz : PSizes H) : 8 * H.W ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_using []
theorem PSizes.o_W8_le_hkO (hz : PSizes H) : 8 * H.W ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_intO (hz : PSizes H) : 8 * H.W ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_st0O (hz : PSizes H) : 8 * H.W ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_st1O (hz : PSizes H) : 8 * H.W ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_stSO (hz : PSizes H) : 8 * H.W ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_stWO (hz : PSizes H) : 8 * H.W ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_sv (hz : PSizes H) : 8 * H.W ≤ H.sv := by
  simp only [Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_tO (hz : PSizes H) : 8 * H.W ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_uO (hz : PSizes H) : 8 * H.W ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_cO_64d8_le_outO_16 (hz : PSizes H) : H.cO + 64 / 8 ≤ H.outO + 16 := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N4; omega_using []
theorem PSizes.o_cO_8_le_L (hz : PSizes H) : H.cO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.cO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_hkO_D_le_L (hz : PSizes H) : H.hkO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_hkO_lt_p31 (hz : PSizes H) : H.hkO < 2 ^ 31 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_intO_4_le_L (hz : PSizes H) : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_intO_lt_p31 (hz : PSizes H) : H.intO < 2 ^ 31 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_outO_16_le_L (hz : PSizes H) : H.outO + 16 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_outO_16_lt_p64 (hz : PSizes H) : H.outO + 16 < 2 ^ 64 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_outO_64d8_le_outO_16 (hz : PSizes H) : H.outO + 64 / 8 ≤ H.outO + 16 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N4; omega_using []
theorem PSizes.o_outO_8_le_L (hz : PSizes H) : H.outO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_outO_8_le_cO (hz : PSizes H) : H.outO + 8 ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_outO_le_cO (hz : PSizes H) : H.outO ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_2mS_le_L (hz : PSizes H) : H.st0O + 2 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st0O_2mS_le_tO (hz : PSizes H) : H.st0O + 2 * H.S ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_3mS_le_L (hz : PSizes H) : H.st0O + 3 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st0O_S_le_L (hz : PSizes H) : H.st0O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st0O_S_le_hkO (hz : PSizes H) : H.st0O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_S_le_st0O_3mS (hz : PSizes H) : H.st0O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_S_le_st1O (hz : PSizes H) : H.st0O + H.S ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_S_le_stSO (hz : PSizes H) : H.st0O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_le_st0O (hz : PSizes H) : H.st0O ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_le_st1O (hz : PSizes H) : H.st0O ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_le_stSO (hz : PSizes H) : H.st0O ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_lt_p31 (hz : PSizes H) : H.st0O < 2 ^ 31 := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_st1O_S_le_L (hz : PSizes H) : H.st1O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st1O_S_le_hkO (hz : PSizes H) : H.st1O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_S_le_st0O_3mS (hz : PSizes H) : H.st1O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_S_le_stSO (hz : PSizes H) : H.st1O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_S_le_stWO (hz : PSizes H) : H.st1O + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_S_le_uO (hz : PSizes H) : H.st1O + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_lt_p31 (hz : PSizes H) : H.st1O < 2 ^ 31 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_stSO_S_le_L (hz : PSizes H) : H.stSO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_stSO_S_le_st0O_3mS (hz : PSizes H) : H.stSO + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stSO_S_le_stWO (hz : PSizes H) : H.stSO + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stSO_hsS_le_L (hz : PSizes H) : H.stSO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stSO_lt_p31 (hz : PSizes H) : H.stSO < 2 ^ 31 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_stWO_S_le_L (hz : PSizes H) : H.stWO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_stWO_S_le_intO (hz : PSizes H) : H.stWO + H.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stWO_S_le_uO (hz : PSizes H) : H.stWO + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stWO_hsS_le_L (hz : PSizes H) : H.stWO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_hsS_le_hkO (hz : PSizes H) : H.stWO + H.stream.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_hsS_le_intO (hz : PSizes H) : H.stWO + H.stream.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_le_intO (hz : PSizes H) : H.stWO ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stWO_le_tO (hz : PSizes H) : H.stWO ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stWO_lt_p31 (hz : PSizes H) : H.stWO < 2 ^ 31 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_sv_64_le_L (hz : PSizes H) : H.sv + 64 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_tO_D_le_L (hz : PSizes H) : H.tO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_tO_lt_p31 (hz : PSizes H) : H.tO < 2 ^ 31 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_uO_D_le_L (hz : PSizes H) : H.uO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_uO_D_le_tO (hz : PSizes H) : H.uO + H.D ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_uO_lt_p31 (hz : PSizes H) : H.uO < 2 ^ 31 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_so_48_le_L (hz : PSizes H) : H.P.so + 48 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have := hz.z.fits; omega_arith
theorem PSizes.o_so_48_le_W8 (hz : PSizes H) : H.P.so + 48 ≤ 8 * H.W := by
  have := hz.z.D.2.1; have := hz.z.fits; omega_arith
theorem PSizes.o_stWO_le_uO (hz : PSizes H) : H.stWO ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_S_eq_st1O (_hz : PSizes H) : H.st0O + H.S = H.st1O := rfl
theorem PSizes.o_st0O_le_stWO (hz : PSizes H) : H.st0O ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_hkO_N_le_L (hz : PSizes H) : H.hkO + H.P.N ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st0O_le_hkO (hz : PSizes H) : H.st0O ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_D_le_B (hz : PSizes H) : H.D ≤ H.P.B := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_sv_64_le_stWO (hz : PSizes H) : H.sv + 64 ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_3mS_le_stWO (hz : PSizes H) : H.st0O + 3 * H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_B_5_le_L (hz : PSizes H) : H.P.B + 5 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end

end


/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`, correct

`pbkdf2` saves our caller's registers, makes the key (hashing a password
longer than a block), HMAC's states for it and the inner state after the salt;
then each block `i` of the output is `U₁` (`update` with `INT (i)` and HMAC's
`finalize`), `iterate` from it, and as much of `T_i` as the output still
needs.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK ea_nat wp_mov32r zx32 contains_pre)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne InRegions.right' sub_of_off sub_of_self bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep bytesAt_getD' writeBytes_at xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-! ## The entry -/

omit hp hz in
/-- After `scratch` is loaded. -/
structure Loaded (s₀ s : State) : Prop where
  r8 : s.gpr .r8 = scr s₀
  r10 : s.gpr .r10 = s₀.gpr .r8
  other : ∀ r, r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

omit hz in
theorem loadScr_ok : WP isa (.block Hash.loadScr) s₀ (Loaded s₀) := by
  simp only [Hash.loadScr]
  refine wp_mov fun s₁ u₁ _ _ => ?_
  refine wp_movm (a := s₀.gpr .rsp + BitVec.ofNat 64 16) (by rw [ea_nat, u₁.other _ (by decide)]) ?_
    fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁.rd, u₁.wr, hp.rd]
    exact ⟨argR s₀, by simp, show (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Contains _ 8 from
      Offset.contains _ (by decide) (by decide) (by decide)⟩
  · rw [u₂.gpr, u₁.mem]; rfl
  · rw [u₂.other _ (by decide), u₁.gpr]
  · intro r h₁ h₂; rw [u₂.other r h₁, u₁.other r h₂]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

theorem entry_ok {s₂ : State} (hl₂ : Loaded s₀ s₂) : WP isa (.block H.entry) s₂ fun s => KR (H := H) s₀ s ∧
    s.gpr .rbx = pw s₀ ∧ s.gpr .rbp = s₀.gpr .rsi ∧ s.gpr .r12 = salt s₀ ∧ s.gpr .r13 = s₀.gpr .rcx ∧
    s.cf = some (decide (pwl s₀ < H.P.B + 1)) := by
  have hW := hz.W
  have := hp.snw; have hc0 := hp.c0
  have hS : H.S = H.P.N + H.P.B := rfl
  simp only [Hash.entry]
  have h8 : s₂.gpr .r8 = scr s₀ := hl₂.r8
  have g₂ : ∀ r, r ≠ .r8 → r ≠ .r10 → s₂.gpr r = s₀.gpr r := hl₂.other
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.save_ok H.hh h8 hW (L := (H.W + H.S) * 8)
    (by rw [hl₂.wr]; exact sc_mem hp) (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L)
    fun s₃ g₃ rd₃ wr₃ f₃ sv₃ => ?_
  refine wp_mov fun s₄ u₄ _ _ => ?_
  have h15 : s₄.gpr .r15 = scr s₀ := by rw [u₄.gpr, g₃, h8]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, wr₃, hl₂.wr]
  refine wp_store (a := A s₀ H.outO) (by rw [ea_nat, h15]) (in_sc hp hz wr₄ (by exact hz.o_outO_8_le_L))
    fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_mov32r fun s₆ u₆ => wp_subi fun s₇ u₇ _ => ?_
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, wr₅, wr₄]
  have h15' : s₆.gpr .r15 = scr s₀ := by rw [u₆.other _ (by decide), g₅, h15]
  refine wp_store (a := A s₀ H.cO) (by rw [ea_nat, u₇.other _ (by decide), h15'])
    (by rw [u₇.wr, wr₆]; exact in_sc hp hz rfl (by exact hz.o_cO_8_le_L)) fun s₈ g₈ m₈ rd₈ wr₈ => ?_
  refine wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ => wp_mov fun s₁₁ u₁₁ _ _ =>
    wp_mov fun s₁₂ u₁₂ _ _ => wp_cmpi fun s₁₃ g₁₃ m₁₃ rd₁₃ wr₁₃ c₁₃ _ => WP.block_nil ?_
  -- The registers.
  have g : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r8 → r ≠ .r10 →
      s₁₃.gpr r = s₀.gpr r := fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => by
    rw [g₁₃, u₁₂.other r h₆, u₁₁.other r h₅, u₁₀.other r h₄, u₉.other r h₃, g₈, u₇.other r h₁, u₆.other r h₁,
      g₅, u₄.other r h₂, g₃, g₂ r h₇ h₈]
  have gs : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s₈.gpr r = s₂.gpr r :=
    fun r h₁ h₂ _ _ _ _ => by rw [g₈, u₇.other r h₁, u₆.other r h₁, g₅, u₄.other r h₂, g₃]
  have rax₈ : s₇.gpr .rax = BitVec.ofNat 64 (cc s₀ - 1) := by
    rw [u₇.gpr, u₆.gpr, g₅, u₄.other _ (by decide), g₃, hl₂.r10, zx32, sx1,
      ofNat_pred hc0]
  have r9₄ : s₄.gpr .r9 = out s₀ := by rw [u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  -- The memory.
  have m₁₃ : s₁₃.mem = (s₃.mem.writeW (A s₀ H.outO) (out s₀)).writeW (A s₀ H.cO)
      (BitVec.ofNat 64 (cc s₀ - 1)) := by
    rw [m₁₃, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈, u₇.mem, u₆.mem, m₅, u₄.mem, r9₄, rax₈]
  have dOC : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.cO, 8⟩ := part_disj hz (Or.inl (by exact hz.o_outO_8_le_cO)) (by exact hz.o_outO_8_le_L) (by exact hz.o_cO_8_le_L)
  have fW : Frame [sR s₀ H.outO 16] s₃.mem s₁₃.mem := by
    rw [m₁₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl _) (by exact hz.o_outO_64d8_le_outO_16)
      (by exact hz.o_outO_16_lt_p64))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by exact hz.o_outO_le_cO) (by exact hz.o_cO_64d8_le_outO_16) (by exact hz.o_outO_16_lt_p64))
  have f₀ : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s₁₃.mem := by
    have e₂ : s₂.mem = s₀.mem := hl₂.mem
    rw [← e₂]
    refine (f₃.sub fun r hr => ?_).trans (fW.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR (H := H) s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR (H := H) s₀, by simp, part_sub (by exact hz.o_outO_16_le_L)⟩
  have sv : SavedRegs H.hh (scr s₀) s₀ s₃.mem :=
    ⟨by rw [sv₃.rbx, g₂ _ (by decide) (by decide)], by rw [sv₃.rbp, g₂ _ (by decide) (by decide)],
      by rw [sv₃.r12, g₂ _ (by decide) (by decide)], by rw [sv₃.r13, g₂ _ (by decide) (by decide)],
      by rw [sv₃.r14, g₂ _ (by decide) (by decide)], by rw [sv₃.r15, g₂ _ (by decide) (by decide)]⟩
  refine ⟨⟨by rw [rd₁₃, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, rd₈, u₇.rd, u₆.rd, rd₅, u₄.rd, rd₃, hl₂.rd],
    by rw [wr₁₃, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈, u₇.wr, wr₆],
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), g₈, u₇.other _ (by decide), h15'],
    SavedRegs.frame H.hh sv fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (a := 8 * H.W) (m := 48) (Or.inl (by exact hz.o_W8_48_le_outO)) (by exact hz.o_W8_48_le_L) (by exact hz.o_outO_16_le_L),
    by rw [m₁₃, readW_writeW_ne _ _ dOC, Mem.readW_writeW_self64],
    by rw [m₁₃, Mem.readW_writeW_self64], f₀⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [c₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide), sx_ofNat (by exact hz.o_B_1_lt_p31), toNat_ofNat_lt (by exact hz.o_B_1_lt_p64)]

/-! ## Helpers -/

omit hp hz in
theorem KR.same {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) (hm : s'.mem = s.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h) (fun _ h => by simp at h)

omit hp hz in
theorem KR.upd {s s' : State} (h : KR (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ≠ .r15 ∧ d ≠ .rsp) : KR (H := H) s₀ s' :=
  h.same u.rd u.wr (u.other _ hd.2.symm) (u.other _ hd.1.symm) u.mem

omit hp hz in
/-- `d ← scratch + o`. -/
theorem scr_ok {s : State} {d : Reg} (h15 : s.gpr .r15 = scr s₀) {o : Nat} (ho : o < 2 ^ 31)
    {rest : List Instr} {Q : State → Prop} (k : ∀ s', Upd s s' d (A s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Pbkdf2.Md.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr],
    by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, h15, sx_ofNat ho]

omit hp hz in
theorem stk_sub {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) :
    Region.Sub (below (s.gpr .rsp) n) (stkR s₀) := by
  rw [h.rsp]; exact below_stk hn

omit hz in
theorem stk_sc {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) {R : Region}
    (hR : Region.Sub R (scR (H := H) s₀)) : (below (s.gpr .rsp) n).Disjoint R :=
  (hp.stk_s.sub_left (stk_sub h hn)).sub_right hR

omit hz in
theorem in_wr {s : State} (h : KR (H := H) s₀ s) : scR (H := H) s₀ ∈ s.wr := by rw [h.wr]; exact sc_mem hp

omit hz in
/-- The parts of `scratch` the functions we call get, as covered regions. -/
theorem cov_part {s : State} (h : KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  sub_of_off (in_wr hp h) hon

omit hz in
theorem cov_low {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (⟨scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (in_wr hp h) hn

/-! ## The key -/

/-- The key HMAC's `init` gets: the password, or the digest of a password
longer than a block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = pw s₀ ∧ kl = pwl s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

omit hp hz in
theorem hash_len (hH : HashOK H) (m : List Byte) : (hH.SH.H.hash m).length = H.D := by
  rw [hH.hash, List.length_take, VG.Proof.MdStream.Md.hash, hH.md.digest_length]; have := hH.hDN; omega_arith

omit hp hz in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash (hH : HashOK H) {k : List Byte} (hk : H.P.B < k.length) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hl := hash_len hH k; have hB := hH.hB; have := hH.hDL
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.P.B < H.D by omega_arith))]

omit hp hz in
theorem blockKey_length (hH : HashOK H) (k : List Byte) : (blockKey hH.SH.H k).length = H.P.B := by
  have hB := hH.hB; have := hH.hDL
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hash_len]; omega_arith
  · omega_arith

omit hp hz in
/-- What the entry sets up, kept until the salt is absorbed. -/
structure KE (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  rbx : s.gpr .rbx = pw s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = salt s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx

/-- The registers `KE` fixes. -/
abbrev eregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

omit hp hz in
theorem KE.upd {s s' : State} (h : KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ eregs) : KE (H := H) s₀ s' := by
  have ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u ⟨(ne _ (by simp)).symm, (ne _ (by simp)).symm⟩, by rw [u.other _ (ne _ (by simp)), h.rbx],
    by rw [u.other _ (ne _ (by simp)), h.rbp], by rw [u.other _ (ne _ (by simp)), h.r12],
    by rw [u.other _ (ne _ (by simp)), h.r13]⟩

theorem KE.call {s s' : State} (h : KE (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz hrd hwr hcs hn hf hw, by rw [hcs _ (by simp [calleeSaved]), h.rbx],
    by rw [hcs _ (by simp [calleeSaved]), h.rbp], by rw [hcs _ (by simp [calleeSaved]), h.r12],
    by rw [hcs _ (by simp [calleeSaved]), h.r13]⟩

/-! ### Hashing a password longer than a block -/

omit hp in
theorem hk1_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .rdi = A s₀ H.stWO := by
  have hB := hz.z.B_le
  have hD := hz.z.D
  rw [← List.append_nil (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)]
  exact scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), u₁.gpr⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hdi : s.gpr .rdi = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  exact VG.Proof.Pbkdf2.Md.X86_64.Calls.init_call hH.stream (st := A s₀ H.stWO) hdi
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by exact hz.o_stWO_hsS_le_L))
    (stk_sc hp h.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))) fun s₂ a₂ r₂ =>
      ⟨h.call hp hz a₂.rd a₂.wr a₂.cs (by decide) a₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩, r₂⟩

/-- `update`'s arguments: the password. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx),
      .mov .rcx (.reg .rbp), .mov .r8 (.reg .r15)] : List Instr))) s fun t => KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream t (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  have k₇ := ((((h.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇
    (by decide)
  refine ⟨k₇, ?_, by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact hr⟩
  exact
    { rdi := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr]
      rdx := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbx]
      rcx := by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbp]
      r8 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₇.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₇.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp k₇.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := hp.pw_s.sub_right (part_sub (by exact hz.o_stWO_hsS_le_L))
      d_sc := hp.pw_s.sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L))
      stk_st := stk_sc hp k₇.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := (hp.stk_pw.sub_left (stk_sub k₇.kr (by decide)))
      stk_sc := stk_sc hp k₇.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀))
    (hsi : s.gpr .rsi = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream ua (by have := hp.pwnw; omega_arith) fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈.rd a₈.wr a₈.cs (by decide) a₈.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · have := r₈ [] hr hsi
    rwa [List.nil_append, h.kr.pwBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov .rsi (.reg .rbp)] : List Instr) ++
      VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++ ([.mov .rcx (.reg .r15)] : List Instr))) s fun t =>
      KE (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀) ∧
      t.gpr .rsi = s₀.gpr .rsi ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  simp only [List.append_assoc]
  refine scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ _ _ => ?_
  refine scr_ok (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]) (by exact hz.o_hkO_lt_p31)
    fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ _ _ => WP.block_nil ?_
  have k₁₂ := (((h.upd u₉ (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide)).upd u₁₂ (by decide)
  refine ⟨k₁₂, ?_, by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
    h.rbp], by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]; exact hr⟩
  exact
    { rdi := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr]
      rdx := by rw [u₁₂.other _ (by decide), u₁₁.gpr]
      rcx := by rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₁₂.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_part hp k₁₂.kr (by rw [hF]; exact hz.o_hkO_N_le_L)
        · exact cov_low hp k₁₂.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_o := part_disj hz (Or.inl (by exact hz.o_stWO_hsS_le_hkO)) (by exact hz.o_stWO_hsS_le_L) (by rw [hF]; exact hz.o_hkO_N_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      o_sc := (low_disj hz (by exact hz.o_W8_le_hkO) (by rw [hF]; exact hz.o_hkO_N_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      stk_st := stk_sc hp k₁₂.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_o := stk_sc hp k₁₂.kr (by decide) (part_sub (by rw [hF]; exact hz.o_hkO_N_le_L))
      stk_sc := stk_sc hp k₁₂.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (fa : VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀))
    (hsi : s.gpr .rsi = s₀.gpr .rsi) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃.rd a₁₃.wr a₁₃.cs (by decide) a₁₃.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_hkO, by rw [hF]; exact hz.o_hkO_N_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · rw [bytesAt_take _ _ hD.2.1]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .rsi).isLt)
      (by rw [hsi, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr))) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧ t.mem = s.mem := by
  have hD := hz.z.D; have hN := hz.z.N
  have hB := hz.z.B_le
  refine scr_ok h.kr.r15 (by exact hz.o_hkO_lt_p31) fun s₁₄ u₁₄ => wp_mov32i fun s₁₅ u₁₅ _ _ => WP.block_nil ?_
  exact ⟨(h.upd u₁₄ (by decide)).upd u₁₅ (by decide), by rw [u₁₅.other _ (by decide), u₁₄.gpr],
    by rw [u₁₅.gpr, zx_ofNat (by exact hz.o_D_lt_p32), toNat_ofNat_lt (by exact hz.o_D_lt_p64)], by rw [u₁₅.mem, u₁₄.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

omit hp hz in
/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if pwl s₀ < H.P.B + 1 then pw s₀ else A s₀ H.hkO
omit hp hz in
abbrev kl (H : Hash) (s₀ : State) : Nat := if pwl s₀ < H.P.B + 1 then pwl s₀ else H.D

theorem key_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hcf : s.cf = some (decide (pwl s₀ < H.P.B + 1))) :
    WP isa H.key s fun t => KE (H := H) s₀ t ∧ t.gpr .rdx = kp H s₀ ∧ (t.gpr .rcx).toNat = kl H s₀ ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hD := hz.z.D
  unfold Hash.key
  refine WP.ite (!decide (pwl s₀ < H.P.B + 1)) (by simp [eval, hcf]) (fun hT => ?_) fun hF => ?_
  · have hlong : ¬ pwl s₀ < H.P.B + 1 := of_decide_eq_false (Bool.not_eq_true' _ ▸ hT)
    have e₁ : kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    have e₂ : kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    rw [e₁, e₂]
    refine WP.mono (hashKey_ok hp hz hH h) fun t ⟨k, rdx, rcx, hb⟩ =>
      ⟨k, rdx, rcx, ⟨.inr ⟨rfl, rfl⟩, by exact hz.o_D_le_B, ?_⟩⟩
    rw [hb, blockKey_hash hH (by rw [bytesAt_length]; omega_arith)]
  · have hshort : pwl s₀ < H.P.B + 1 := of_decide_eq_true (by simpa using hF)
    have e₁ : kp H s₀ = pw s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    have e₂ : kl H s₀ = pwl s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    rw [e₁, e₂]
    refine wp_mov fun t₁ u₁ _ _ => wp_mov fun t₂ u₂ _ _ => WP.block_nil ?_
    refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.rbx],
      by rw [u₂.gpr, u₁.other _ (by decide), h.rbp], ⟨.inl ⟨rfl, rfl⟩, by omega_arith, ?_⟩⟩
    rw [u₂.mem, u₁.mem, h.kr.pwBytes hp]

/-! ## HMAC's states -/

omit hp hz in
theorem repr_keep (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.stream.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega_arith) hi) hr

omit hp hz in
/-- A state copied from `p` to `q` represents the same message. -/
theorem repr_copy (hH : HashOK H) {m : Mem} {p q : Addr} {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr (writeBytes m q (bytesAt m p H.S)) q msg := by
  have : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega_arith
  refine hH.stream.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_arith),
    bytesAt_getD' _ _ (show i < H.S from hi)]

/-- `K₀`, the password as a key. -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- HMAC's states in `scratch`: `K₀ ⊕ ipad`, `K₀ ⊕ opad`, and `K₀ ⊕ ipad`
after the salt. -/
structure States (hH : HashOK H) (s₀ : State) (m : Mem) : Prop where
  i : hH.SH.Repr m (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad)
  o : hH.SH.Repr m (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)
  s : hH.SH.Repr m (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad ++ bytesAt s₀.mem (salt s₀) (sl s₀))

omit hp in
theorem States.keep (hH : HashOK H) {m m' : Mem} (h : States hH s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ H.st0O (3 * H.S)) r) : States hH s₀ m' := by
  exact ⟨repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by exact hz.o_st0O_S_le_st0O_3mS))) h.i,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_st0O_3mS))) h.o,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_st0O_3mS))) h.s⟩

omit hz in
/-- Regions a call writes, disjoint from a part of `scratch`. -/
theorem disj_call {s : State} (h : KR (H := H) s₀ s) {X : Region} (hX : Region.Sub X (scR (H := H) s₀))
    {ws : List Region} {n : Nat} (hn : n ≤ 24) (hw : ∀ r ∈ ws, X.Disjoint r) :
    ∀ r ∈ ws ++ [below (s.gpr .rsp) n], X.Disjoint r := fun r hr => by
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (stk_sc hp h hn hX).symm

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : KeyAt hH s₀ m kp kl) {s : State}
    (h : KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st0O, H.S⟩ ∧
      Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st1O, H.S⟩ ∧ Region.Disjoint ⟨kp, kl⟩ (lowR (H := H) s₀) ∧
      (below (s.gpr .rsp) 24).Disjoint ⟨kp, kl⟩ := by
  have hD := hz.z.D; have hN := hz.z.N
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.pw_s.sub_right (part_sub (by exact hz.o_st0O_S_le_L)), hp.pw_s.sub_right (part_sub (by exact hz.o_st1O_S_le_L)),
      hp.pw_s.sub_right low_sub, hp.stk_pw.sub_left (stk_sub h (Nat.le_refl _))⟩
  · refine ⟨Covers.of_sub fun r hr => ?_, part_disj hz (Or.inr (by exact hz.o_st0O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st0O_S_le_L),
      part_disj hz (Or.inr (by exact hz.o_st1O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st1O_S_le_L), low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_D_le_L),
      stk_sc hp h (Nat.le_refl _) (part_sub (by exact hz.o_hkO_D_le_L))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := cov_part hp h (o := H.hkO) (n := H.D) (by exact hz.o_hkO_D_le_L)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-- HMAC's `init`'s arguments: its two states and the key. -/
theorem su1_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hdx : s.gpr .rdx = kp H s₀)
    (hcx : (s.gpr .rcx).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.st0O ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rsi H.st1O ++
      ([.mov .r8 (.reg .r15)] : List Instr))) s fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  simp only [List.append_assoc]
  refine scr_ok h.kr.r15 (by exact hz.o_st0O_lt_p31) fun s₁ u₁ => ?_
  refine scr_ok (by rw [u₁.other _ (by decide), h.kr.r15]) (by exact hz.o_st1O_lt_p31) fun s₂ u₂ => wp_mov fun s₃ u₃ _ _ =>
    WP.block_nil ?_
  have k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { rdi := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      rsi := by rw [u₃.other _ (by decide), u₂.gpr]
      rdx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdx]
      rcx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hcx]
      r8 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.r15]
      klB := hk.le
      cr := kc
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₃.kr (by exact hz.o_st0O_S_le_L)
        · exact cov_part hp k₃.kr (by exact hz.o_st1O_S_le_L)
        · exact cov_low hp k₃.kr (by exact hz.o_W8_le_L)
      i_o := part_disj hz (Or.inl (by exact hz.o_st0O_S_le_st1O)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_st1O_S_le_L)
      i_s := low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_S_le_L)
      o_s := low_disj hz (by exact hz.o_W8_le_st1O) (by exact hz.o_st1O_S_le_L)
      k_i := k_i
      k_o := k_o
      k_s := k_s
      stk_i := stk_sc hp k₃.kr (Nat.le_refl _) (part_sub (by exact hz.o_st0O_S_le_L))
      stk_o := stk_sc hp k₃.kr (Nat.le_refl _) (part_sub (by exact hz.o_st1O_S_le_L))
      stk_k := k_stk
      stk_s := stk_sc hp k₃.kr (Nat.le_refl _) low_sub
      scnw := by show (scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega_arith }

/-- HMAC's `init`: the key's inner and outer states. -/
theorem su2_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀))
    (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine hinit_call hH hI hIsp hId ia fun s₄ rd₄ wr₄ cs₄ f₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.call hp hz rd₄ wr₄ cs₄ (Nat.le_refl _) f₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_st0O_S_le_L⟩
      · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_st1O, by exact hz.o_st1O_S_le_L⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · rw [hk.k0] at ri₄; exact ri₄
  · rw [hk.k0] at ro₄; exact ro₄

/-- The inner state copied, and `update`'s arguments: the salt. -/
theorem su3_ok (hH : HashOK H) {s₄ : State} (h : KE (H := H) s₀ s₄)
    (ri₄ : hH.SH.Repr s₄.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro₄ : hH.SH.Repr s₄.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)) :
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.st0O .r15 H.stSO H.S)
      (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stSO ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 H.P.B)),
        .mov .rdx (.reg .r12), .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)] : List Instr)))) s₄ fun t =>
      KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream t (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 H.P.B ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) ∧
      hH.SH.Repr t.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide) (by decide)
    (so := H.st0O) (d := H.stSO) (n := H.S) (by exact hz.o_0_lt_S) (by exact hz.o_S_lt_p31) (s := s₄)
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_st0O_S_le_L])))
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stSO_S_le_L]))
    (by rw [h.kr.r15]; exact part_disj hz (Or.inl (by exact hz.o_st0O_S_le_stSO)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_stSO_S_le_L))) fun s₅ c₅ => ?_)
  rw [h.kr.r15] at c₅
  have f₅ : Frame [sR s₀ H.stSO H.S] s₄.mem s₅.mem := by
    rw [c₅.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have k₅ : KE (H := H) s₀ s₅ := ⟨h.kr.write hz c₅.rd c₅.wr (c₅.other _ (by decide) (by decide))
      (c₅.other _ (by decide) (by decide)) (o := H.stSO) (n := H.S) (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_L) f₅,
    by rw [c₅.other _ (by decide) (by decide), h.rbx], by rw [c₅.other _ (by decide) (by decide), h.rbp],
    by rw [c₅.other _ (by decide) (by decide), h.r12], by rw [c₅.other _ (by decide) (by decide), h.r13]⟩
  have dS : ∀ o, o + H.S ≤ H.stSO → ∀ r ∈ [sR s₀ H.stSO H.S], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_S_le_L)
  have ri₅ := repr_keep hH f₅ (dS _ (by exact hz.o_st0O_S_le_stSO)) ri₄
  have ro₅ := repr_keep hH f₅ (dS _ (by exact hz.o_st1O_S_le_stSO)) ro₄
  have rs₅ : hH.SH.Repr s₅.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by rw [c₅.mem]; exact repr_copy hH ri₄
  refine scr_ok k₅.kr.r15 (by exact hz.o_stSO_lt_p31) fun s₆ u₆ => wp_mov32i fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ =>
    wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ => WP.block_nil ?_
  have k₁₀ := ((((k₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
    (by decide)
  have m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  refine ⟨k₁₀, ?_, by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      zx_ofNat (by exact hz.o_B_lt_p32)], m₁₀ ▸ ri₅, m₁₀ ▸ ro₅, m₁₀ ▸ rs₅⟩
  exact
    { rdi := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), u₆.gpr]
      rdx := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.r12]
      rcx := by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.r13]
      r8 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₁₀.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₁₀.kr (by exact hz.o_stSO_hsS_le_L)
        · exact cov_low hp k₁₀.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stSO) (by exact hz.o_stSO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := hp.sa_s.sub_right (part_sub (by exact hz.o_stSO_hsS_le_L))
      d_sc := hp.sa_s.sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L))
      stk_st := stk_sc hp k₁₀.kr (by decide) (part_sub (by exact hz.o_stSO_hsS_le_L))
      stk_d := hp.stk_sa.sub_left (stk_sub k₁₀.kr (by decide))
      stk_sc := stk_sc hp k₁₀.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

/-- `update` with the salt. -/
theorem su4_ok (hH : HashOK H) {s₁₀ : State} (k₁₀ : KE (H := H) s₀ s₁₀)
    (ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s₁₀ (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀))
    (hsi : s₁₀.gpr .rsi = BitVec.ofNat 64 H.P.B)
    (ri : hH.SH.Repr s₁₀.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro : hH.SH.Repr s₁₀.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad))
    (rs : hH.SH.Repr s₁₀.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad)) :
    WP isa (.call H.updN H.updC) s₁₀ fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream ua (by have := hp.sanw; omega_arith) fun s₁₁ a₁₁ r₁₁ => ?_
  have k₁₁ := k₁₀.call hp hz a₁₁.rd a₁₁.wr a₁₁.cs (by decide) a₁₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stSO, by exact hz.o_stSO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  have dW : ∀ o, H.st0O ≤ o → o + H.S ≤ H.stSO → ∀ r ∈ [(⟨A s₀ H.stSO, H.stream.S⟩ : Region), ⟨scr s₀, hH.stream.Wb⟩] ++
      [below (s₁₀.gpr .rsp) 16], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho₀ ho =>
    disj_call hp k₁₀.kr (part_sub (by omega_using [ho, hz.o_stSO_S_le_L])) (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_hsS_le_L)
      · exact (low_disj hz (by omega_using [ho₀, hz.o_W8_le_st0O]) (by omega_using [ho, hz.o_stSO_S_le_L])).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
  refine ⟨k₁₁, repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st0O) (by exact hz.o_st0O_S_le_stSO)) ri,
    repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_stSO)) ro, ?_⟩
  have := r₁₁ _ rs (by rw [hsi, xorPad_length, blockKey_length])
  rwa [k₁₀.kr.saltBytes hp] at this

theorem setup_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : KE (H := H) s₀ s)
    (hdx : s.gpr .rdx = kp H s₀) (hcx : (s.gpr .rcx).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa H.setup s fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  unfold Hash.setup
  refine WP.seq (WP.mono (su1_ok hp hz hH h hdx hcx hk) fun s₁ ⟨k₁, a₁, h₁⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hH hI hIsp hId k₁ a₁ h₁) fun s₂ ⟨k₂, i₂, o₂⟩ => ?_)
  refine WP.assoc (WP.seq (WP.mono (su3_ok hp hz hH k₂ i₂ o₂) fun s₃ ⟨k₃, a₃, si₃, i₃, o₃, r₃⟩ => ?_))
  exact su4_ok hp hz hH k₃ a₃ si₃ i₃ o₃ r₃

end

end VG.Proof.Pbkdf2.Md.X86_64.Pbk
