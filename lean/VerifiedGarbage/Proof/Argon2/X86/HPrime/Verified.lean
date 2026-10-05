import VerifiedGarbage.Proof.Blake2.X86.Blake2b
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Argon2.X86.HPrime
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified
import VerifiedGarbage.Spec.Argon2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.HPrime.Calls`. -/
section

section

/-!
# Argon2 H′ on x86 (32-bit): the contract of the proof

`hPrimeX86`: `vg_argon2_hprime(input, input_len, out, out_len, scratch)` with
its arguments only read; `Spec.Argon2.hPrimeContract`, which lets the code
write them, is reached by narrowing. H′ uses the 60 bytes of stack below its
return address: a call of `vg_blake2b_update` pushes six words and its return
address, and `update` itself uses 32 bytes.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

def hPrimeX86 : Contract X86.isa where
  pre s :=
    let input : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
    let out : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, 16384⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := below (s.gpr .esp) 60
    s.rd = [input, args] ∧ s.wr = [out, scratch] ∧
    input.Disjoint scratch ∧ out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint input ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 4).toNat + 16384 ≤ 2 ^ 32 ∧ 60 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 1 ≤ (VG.X86.arg s 3).toNat
  post s s' := bytesAt s'.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat =
    Spec.Argon2.hPrime (VG.X86.arg s 3).toNat (bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

section
variable (s₀ : State)

abbrev inp : BitVec 32 := VG.X86.arg s₀ 0
abbrev inl : Nat := (VG.X86.arg s₀ 1).toNat
abbrev op : BitVec 32 := VG.X86.arg s₀ 2
abbrev ol : Nat := (VG.X86.arg s₀ 3).toNat
abbrev scr : BitVec 32 := VG.X86.arg s₀ 4
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
/-- `scratch`, as an address. -/
abbrev P : Addr := (VG.Proof.Argon2.X86.HPrime.scr s₀).setWidth 64
abbrev inR : Region := ⟨(VG.Proof.Argon2.X86.HPrime.inp s₀).setWidth 64, VG.Proof.Argon2.X86.HPrime.inl s₀⟩
abbrev outR : Region := ⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64, VG.Proof.Argon2.X86.HPrime.ol s₀⟩
abbrev scrR : Region := ⟨VG.Proof.Argon2.X86.HPrime.P s₀, 16384⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(VG.Proof.Argon2.X86.HPrime.esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) 60

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Argon2.X86.HPrime.inR s₀, VG.Proof.Argon2.X86.HPrime.argR s₀]
  wr : s₀.wr = [VG.Proof.Argon2.X86.HPrime.outR s₀, VG.Proof.Argon2.X86.HPrime.scrR s₀]
  in_scr : (VG.Proof.Argon2.X86.HPrime.inR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.scrR s₀)
  out_scr : (VG.Proof.Argon2.X86.HPrime.outR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.scrR s₀)
  arg_out : (VG.Proof.Argon2.X86.HPrime.argR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.outR s₀)
  arg_scr : (VG.Proof.Argon2.X86.HPrime.argR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.scrR s₀)
  ret_out : (VG.Proof.Argon2.X86.HPrime.retR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.outR s₀)
  ret_scr : (VG.Proof.Argon2.X86.HPrime.retR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.scrR s₀)
  stk_in : (VG.Proof.Argon2.X86.HPrime.stkR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.inR s₀)
  stk_out : (VG.Proof.Argon2.X86.HPrime.stkR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.outR s₀)
  stk_scr : (VG.Proof.Argon2.X86.HPrime.stkR s₀).Disjoint (VG.Proof.Argon2.X86.HPrime.scrR s₀)
  in_fits : (VG.Proof.Argon2.X86.HPrime.inp s₀).toNat + VG.Proof.Argon2.X86.HPrime.inl s₀ ≤ 2 ^ 32
  out_fits : (VG.Proof.Argon2.X86.HPrime.op s₀).toNat + VG.Proof.Argon2.X86.HPrime.ol s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Argon2.X86.HPrime.scr s₀).toNat + 16384 ≤ 2 ^ 32
  esp_lo : 60 ≤ (VG.Proof.Argon2.X86.HPrime.esp₀ s₀).toNat
  esp_hi : (VG.Proof.Argon2.X86.HPrime.esp₀ s₀).toNat + 24 ≤ 2 ^ 32
  ol_pos : 1 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀

theorem pre_of (s₀ : State) (h : hPrimeX86.pre s₀) : VG.Proof.Argon2.X86.HPrime.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- `[scratch + d]`, as the code addresses it. -/
theorem scr_addr {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) {d : Nat} (hd : d < 16384) :
    addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d = VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 d := addr_eq (by have := hp.scr_fits; omega)

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the calls of the BLAKE2b functions

`init_ok`, `update_ok`, `finalize_ok`: H′'s macros (`Impl.Argon2.X86.HPrime`)
call the x86 BLAKE2b streaming functions with the state at `scratch` (in
`ebx`, at `B`), their scratch at `scratch + 192`, and the stack below `esp`
(`E`). Each is stated for any `B` and `E`, so that the derivation can use them
too: they write only the state, their scratch, the digest (`finalize`) and
the stack below `E`, and keep `ebx`, `ebp` and `esp`.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (update finalize initCode updateCode finalizeCode initName
  updateName finalizeName)
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86 countX86)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-! ## The callees -/

theorem init_correct : ∀ s, (VG.Proof.Blake2.initX86 b).pre s →
    ∃ t s', Exec isa initCode s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Blake2.initX86 b).post s s' :=
  (Proof.Blake2.X86.Stream.init_verified Proof.Blake2.X86.B.ok Proof.Blake2.X86.B.init_ct
    Proof.Blake2.X86.B.init_implies.sat_left).1

theorem update_correct : ∀ s, (VG.Proof.Blake2.updateX86 b).pre s →
    ∃ t s', Exec isa updateCode s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Blake2.updateX86 b).post s s' :=
  (Proof.Blake2.X86.Stream.update_verified Proof.Blake2.X86.B.ok Proof.Blake2.X86.B.callee
    Proof.Blake2.X86.B.update_ct Proof.Blake2.X86.B.update_implies.sat_left).1

theorem finalize_correct : ∀ s, (VG.Proof.Blake2.finalizeX86 b).pre s →
    ∃ t s', Exec isa finalizeCode s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Blake2.finalizeX86 b).post s s' :=
  (Proof.Blake2.X86.Stream.finalize_verified Proof.Blake2.X86.B.ok Proof.Blake2.X86.B.callee
    Proof.Blake2.X86.B.finalize_ct Proof.Blake2.X86.B.finalize_implies.sat_left).1

theorem init_nosp : NoSp initCode := NoSp.of_all (by lit_decide)
theorem update_nosp : NoSp updateCode := NoSp.of_all (by lit_decide)
theorem finalize_nosp : NoSp finalizeCode := NoSp.of_all (by lit_decide)
theorem init_stack : stackUse initCode = 0 := by lit_decide
theorem update_stack : stackUse updateCode = 32 := by lit_decide
theorem finalize_stack : stackUse finalizeCode = 32 := by lit_decide

/-! ## Regions -/

/-- `[x + d, x + d + n)`, for a buffer at `x` inside the 32-bit address space. -/
theorem setWidth_add {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

/-- What every call needs: `ebx` holds `B`, `esp` is `E`, the state, the
callees' scratch and the digest (`scratch[0, 832)`) are writable, and the 60
bytes below `E` are outside them. -/
structure Ctx (B E : BitVec 32) (s : State) : Prop where
  ebx : s.gpr .ebx = B
  esp : s.gpr .esp = E
  fits : B.toNat + 832 ≤ 2 ^ 32
  lo : 60 ≤ E.toNat
  hi : E.toNat + 4 ≤ 2 ^ 32
  wr : Covers [⟨B.setWidth 64, 832⟩] s.wr
  stk : (below E 60).Disjoint ⟨B.setWidth 64, 832⟩

theorem Ctx.of_regs {B E : BitVec 32} {s t : State} (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) (hb : t.gpr .ebx = s.gpr .ebx)
    (hs : t.gpr .esp = s.gpr .esp) (hw : t.wr = s.wr) : VG.Proof.Argon2.X86.HPrime.Ctx B E t :=
  ⟨hb.trans h.ebx, hs.trans h.esp, h.fits, h.lo, h.hi, hw ▸ h.wr, h.stk⟩

section
variable {B E : BitVec 32} {s : State}

theorem Ctx.sub (_h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {d n : Nat} (hd : d + n ≤ 832) :
    Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 d, n⟩ ⟨B.setWidth 64, 832⟩ :=
  Offset.sub_base _ hd

theorem Ctx.cov (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {d n : Nat} (hd : d + n ≤ 832) :
    Covers [⟨B.setWidth 64 + BitVec.ofNat 64 d, n⟩] s.wr :=
  (Covers.of_sub (rs' := [⟨B.setWidth 64, 832⟩]) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, d, rfl, hd⟩).trans h.wr

theorem Ctx.stk_sub (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {d n k : Nat} (hd : d + n ≤ 832) (hk : k ≤ 60) :
    (below E k).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 d, n⟩ :=
  (h.stk.sub_right (h.sub hd)).sub_left (below_sub hk h.lo)

theorem Ctx.cov0 (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {n : Nat} (hn : n ≤ 832) : Covers [⟨B.setWidth 64, n⟩] s.wr :=
  (Covers.of_sub (rs' := [⟨B.setWidth 64, 832⟩]) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp; omega⟩).trans h.wr

end

theorem covers_ins {rs a b : List Region} (f : Region) (h : Covers rs (a ++ b)) :
    Covers rs (a ++ f :: b) := fun x n hi => InRegions_append_cons.mpr (.inr (h x n hi))

theorem covers_cons {rs b : List Region} (f : Region) (h : Covers rs b) : Covers rs (f :: b) :=
  fun x n hi => let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_cons_of_mem _ hr, hc⟩

theorem covers_frame {E : BitVec 32} {k : Nat} {rd : List Region} {a : Addr}
    (ha : a = (E - BitVec.ofNat 32 k).setWidth 64) (wr : List Region) :
    Covers [⟨a, k⟩] (rd ++ below E k :: wr) := by
  intro x n ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact InRegions_append_cons.mpr (.inl (by subst ha; exact hc))

/-! ## `init` -/

theorem keyBlock_nil (m : Mem) (p : Addr) : keyBlock 64 (bytesAt m p 0) = [] := rfl

theorem init_ok {B E : BitVec 32} {s : State} (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {n : Nat} (hn : s.gpr .edx = BitVec.ofNat 32 n)
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa Impl.Argon2.X86.HPrime.init s fun t => Repr b (Spec.Blake2.init b n 0) t.mem (B.setWidth 64) [] ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨B.setWidth 64, 192⟩, below E 20] s.mem t.mem := by
  unfold Impl.Argon2.X86.HPrime.init
  refine WP.seq (wp_movi fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have rs : [Reg.eax, .ecx, .edx, .ebx] ≠ [] := by simp
  have hrs : Reg.esp ∉ [Reg.eax, .ecx, .edx, .ebx] := by decide
  have esp₂ : s₂.gpr .esp = E := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have fit : 4 * [Reg.eax, .ecx, .edx, .ebx].length + 4 ≤ (s₂.gpr .esp).toNat := by
    rw [esp₂]; have := h.lo; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .ecx, .edx, .ebx] s₂).callEntry with hsE
  have a0 : VG.X86.arg sE 0 = B := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₂.other _ (by decide : Reg.ebx ≠ .ecx), u₁.other _ (by decide : Reg.ebx ≠ .eax), h.ebx]
  have a1 : VG.X86.arg sE 1 = BitVec.ofNat 32 n := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₂.other _ (by decide : Reg.edx ≠ .ecx), u₁.other _ (by decide : Reg.edx ≠ .eax), hn]
  have a2 : VG.X86.arg sE 2 = B := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₂.gpr, u₁.other _ (by decide : Reg.ebx ≠ .eax), h.ebx]
  have a3 : VG.X86.arg sE 3 = 0 := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₂.other _ (by decide : Reg.eax ≠ .ecx), u₁.gpr]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have w₂ : s₂.wr = s.wr := u₂.wr.trans u₁.wr
  have stR : Region.Sub ⟨B.setWidth 64, 192⟩ ⟨B.setWidth 64, 832⟩ := Region.sub_prefix (by decide)
  have d20 : (below E 20).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right stR).sub_left (below_sub (by decide) h.lo)
  refine WP.callWith (k := VG.Proof.Blake2.initX86 b) VG.Proof.Argon2.X86.HPrime.init_correct VG.Proof.Argon2.X86.HPrime.init_nosp rs hrs
    (by rw [VG.Proof.Argon2.X86.HPrime.init_stack, esp₂]; have := h.lo; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨(B.setWidth 64), 0⟩, ⟨argAddr sE 0, 16⟩]) (wr := [⟨B.setWidth 64, 192⟩])
    ⟨?_, ?_, ?_⟩ fun t rd' wr' cs' f' ⟨s₃, m₃, post⟩ => ?_
  · rw [← hsE]
    simp only [VG.Proof.Blake2.initX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    have mb : (64 : Nat) ≤ b.maxBytes := by decide
    refine ⟨rfl, rfl, fun _ h₁ _ => by simp [Region.Contains] at h₁, ?_, ?_,
      by simp only [Proof.Blake2.bufOff, blockBytes]; have := h.fits; omega,
      by simp; have := B.isLt; omega, ?_, by simp [BitVec.toNat_ofNat]; omega,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega, by simp⟩
    · exact d20.sub_left (below_sub (by decide) (by have := h.lo; omega))
    · refine d20.sub_left ?_
      have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega) (by have := h.lo; omega)
      rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
        rw [← VG.Offset.sub_add_eq]; rfl]
      exact this
    · rw [sub_toNat (by have := h.lo; omega)]; have := E.isLt; omega
  · rw [esp₂, w₂]
    refine Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) ?_
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', hc'⟩ := h.wr a k ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains] at hc ⊢; omega⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hc; simpa using hc
    · exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
        ((h.wr.trans fun a k hi => let ⟨r', hr', hc'⟩ := hi
          InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)))
  · rw [esp₂, w₂]
    exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (h.wr.trans fun a k ⟨r', hr', hc'⟩ => ⟨r', List.mem_cons_of_mem _ hr', hc'⟩)
  · rw [← hsE] at post
    simp only [VG.Proof.Blake2.initX86, arg_withRegions, State.withRegions_mem, a0, a1, a3, m₃] at post
    refine ⟨?_, fun r hr => (cs' r hr).trans ?_, rd'.trans (u₂.rd.trans u₁.rd), wr'.trans w₂, ?_⟩
    · have kb : ∀ (m : Mem) (p : Addr), keyBlock 64 (bytesAt m p (BitVec.toNat (0 : BitVec 32))) = [] :=
        fun _ _ => rfl
      rw [kb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)] at post
      exact post
    · have : r ≠ .eax ∧ r ≠ .ecx := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₂.other _ this.2, u₁.other _ this.1]
    · rw [VG.Proof.Argon2.X86.HPrime.init_stack, esp₂] at f'
      rw [← u₁.mem, ← u₂.mem]
      exact f'.mono fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp

/-! ## Streaming states in memory -/

/-- A streaming state is kept while only memory outside its 192 bytes changes. -/
theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 192⟩ r) {h0 : HashValue 64} {d : List Byte}
    (h : Repr b h0 m p d) : Repr b h0 m' p d := by
  have hb : ∀ i < 192, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
    fun i hi => hf.bytes (R := ⟨p, 192⟩) hd (by simp) hi
  obtain ⟨h1, h2⟩ := h
  have hl := Proof.Blake2.bufLen_le (w := 64) (by decide) d.length
  have hs := Proof.Blake2.sub_bufLen (w := 64) d
  have hs' := Proof.Blake2.bufLen_le_self (w := 64) d.length
  refine ⟨?_, ?_⟩
  · rw [Proof.Blake2.stateAt_congr (fun i hi => hb i (by simp only [Proof.Blake2.bufOff] at hi; omega))]
    exact h1
  · rw [← h2]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have hbb : blockBytes 64 = 128 := rfl
    rw [hbb] at hl hs hi
    exact hb _ (by omega)

/-! ## `update` -/

/-- `update` hashes the `L` bytes at `D` (in `esi` and `edi`) into the state at
`B`, whose byte count is in `edx:ecx`. -/
theorem update_ok {B E : BitVec 32} {s : State} (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .esi = D) (hL : (s.gpr .edi).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa VG.Impl.Argon2.X86.HPrime.update s fun t => Repr b h0 t.mem (B.setWidth 64) (d ++ bytesAt s.mem (D.setWidth 64) L) ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨B.setWidth 64, 768⟩, below E 60] s.mem t.mem := by
  unfold VG.Impl.Argon2.X86.HPrime.update
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil ?_)
  have rs : [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] ≠ [] := by simp
  have hrs : Reg.esp ∉ [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] := by decide
  have o₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ hr, u₁.other _ hr]
  have esp₂ : s₂.gpr .esp = E := by rw [o₂ _ (by decide), h.esp]
  have hlo := h.lo
  have fit : 4 * [Reg.eax, .edi, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₂.gpr .esp).toNat := by
    rw [esp₂]; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] s₂).callEntry with hsE
  have a0 : VG.X86.arg sE 0 = B := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .ebx (by decide), h.ebx]
  have a1 : VG.X86.arg sE 1 = s.gpr .ecx := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .ecx (by decide)]
  have a2 : VG.X86.arg sE 2 = s.gpr .edx := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .edx (by decide)]
  have a3 : VG.X86.arg sE 3 = D := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .esi (by decide), hD]
  have a4 : (VG.X86.arg sE 4).toNat = L := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .edi (by decide), hL]
  have a5 : VG.X86.arg sE 5 = B + 192 := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [u₂.gpr, u₁.gpr, h.ebx]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 28 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have w₂ : s₂.wr = s.wr := u₂.wr.trans u₁.wr
  have r₂ : s₂.rd = s.rd := u₂.rd.trans u₁.rd
  have hfit := h.fits
  have e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := VG.Proof.Argon2.X86.HPrime.setWidth_add (d := 192) (by omega)
  have stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    h.stk.sub_right (Region.sub_prefix (by decide))
  have scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  have stk60 : ∀ {k : Nat} {r : Region}, k ≤ 60 → (below E 60).Disjoint r → (below E k).Disjoint r :=
    fun hk d => d.sub_left (below_sub hk hlo)
  have retSub : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 24) (by omega) hlo
    rw [show E - BitVec.ofNat 32 28 = E - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 28) (by omega) hlo
    have e : (E - BitVec.ofNat 32 28 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 28).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega)]; omega)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  have argSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩ (below E 60) :=
    below_sub (by decide) hlo
  have b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega
  refine WP.callWith (k := VG.Proof.Blake2.updateX86 b) VG.Proof.Argon2.X86.HPrime.update_correct VG.Proof.Argon2.X86.HPrime.update_nosp rs hrs
    (by rw [VG.Proof.Argon2.X86.HPrime.update_stack, esp₂]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨D.setWidth 64, L⟩, ⟨argAddr sE 0, 24⟩])
    (wr := [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩])
    ⟨?_, ?_, ?_⟩ fun t rd' wr' cs' f' ⟨s₃, m₃, post⟩ => ?_
  · rw [← hsE]
    simp only [VG.Proof.Blake2.updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, a5, eA, eSp, e192, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact hDs.sub_right (Region.sub_prefix (by decide))
    · exact hDs.sub_right (Offset.sub_base _ (by decide))
    · exact stR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · exact hDk.sub_left calleeStk
    · omega
    · omega
    · rw [b192]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := E.isLt; omega
  · rw [esp₂, w₂, r₂]
    refine Covers.append_left (Covers.cons (VG.Proof.Argon2.X86.HPrime.covers_ins _ hDc) (Covers.cons (VG.Proof.Argon2.X86.HPrime.covers_frame eA _)
      Covers.nil)) (VG.Proof.Argon2.X86.HPrime.covers_ins _ (Covers.right ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))))
  · rw [esp₂, w₂]
    exact VG.Proof.Argon2.X86.HPrime.covers_cons _ ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))
  · rw [VG.Proof.Argon2.X86.HPrime.update_stack, esp₂] at f'
    have hpush : Frame [below E 28] s₂.mem sE.mem := by
      have := callEntry_frame fit hrs; rw [esp₂] at this; exact this
    have mE : s₂.mem = s.mem := u₂.mem.trans u₁.mem
    rw [← hsE] at post
    simp only [VG.Proof.Blake2.updateX86, arg_withRegions, State.withRegions_mem, a0, a3, a4, m₃] at post
    have reprE : Repr b h0 sE.mem (B.setWidth 64) d :=
      VG.Proof.Argon2.X86.HPrime.repr_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (stk60 (by decide) stR).symm) (mE ▸ repr)
    have countE : VG.Proof.Blake2.countX86 (sE.withRegions [⟨D.setWidth 64, L⟩, ⟨argAddr sE 0, 24⟩]
        [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩]) = BitVec.ofNat 64 d.length := by
      simp only [VG.Proof.Blake2.countX86, arg_withRegions]
      rw [hsE, callEntry_arg fit hrs (by simp), callEntry_arg fit hrs (by simp)]
      simpa [o₂ .ecx (by decide), o₂ .edx (by decide)] using hc
    have dataE : bytesAt sE.mem (D.setWidth 64) L = bytesAt s.mem (D.setWidth 64) L := by
      rw [← mE]
      exact Proof.Blake2.bytesAt_congr fun i hi =>
        hpush.bytes (R := ⟨D.setWidth 64, L⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (stk60 (by decide) hDk).symm) (by simp; omega) hi
    have := post h0 d reprE (by simpa using countE) (by omega)
    rw [dataE] at this
    refine ⟨this, fun r hr => (cs' r hr).trans ?_, rd'.trans r₂, wr'.trans w₂, ?_⟩
    · have : r ≠ .eax := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      exact o₂ r this
    · rw [← mE]
      exact f'.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) hlo⟩

/-! ## `finalize` -/

/-- `finalize` writes the hash of the data in the state at `B`, whose byte
count is in `edx:ecx`, to `scratch[768, 832)`. -/
theorem finalize_ok {B E : BitVec 32} {s : State} (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa VG.Impl.Argon2.X86.HPrime.finalize s fun t => bytesAt t.mem (B.setWidth 64 + 768) 64 = finalHash b h0 d ∧
      (∀ r ∈ calleeSaved, r ≠ .esi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨B.setWidth 64, 832⟩, below E 60] s.mem t.mem := by
  unfold VG.Impl.Argon2.X86.HPrime.finalize
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    WP.block_nil ?_)
  have rs : [Reg.eax, .esi, .edx, .ecx, .ebx] ≠ [] := by simp
  have hrs : Reg.esp ∉ [Reg.eax, .esi, .edx, .ecx, .ebx] := by decide
  have o₄ : ∀ r, r ≠ .eax → r ≠ .esi → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₄.other _ h2, u₃.other _ h2, u₂.other _ h1, u₁.other _ h1]
  have esp₄ : s₄.gpr .esp = E := by rw [o₄ _ (by decide) (by decide), h.esp]
  have hlo := h.lo
  have hfit := h.fits
  have fit : 4 * [Reg.eax, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₄.gpr .esp).toNat := by
    rw [esp₄]; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .esi, .edx, .ecx, .ebx] s₄).callEntry with hsE
  have a0 : VG.X86.arg sE 0 = B := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₄ .ebx (by decide) (by decide), h.ebx]
  have a1 : VG.X86.arg sE 1 = s.gpr .ecx := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₄ .ecx (by decide) (by decide)]
  have a2 : VG.X86.arg sE 2 = s.gpr .edx := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₄ .edx (by decide) (by decide)]
  have a3 : VG.X86.arg sE 3 = B + 768 := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₄.gpr, u₃.gpr, u₂.other _ (by decide : Reg.ebx ≠ .eax), u₁.other _ (by decide : Reg.ebx ≠ .eax),
      h.ebx]
  have a4 : VG.X86.arg sE 4 = B + 192 := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₄.other _ (by decide : Reg.eax ≠ .esi), u₃.other _ (by decide : Reg.eax ≠ .esi), u₂.gpr, u₁.gpr,
      h.ebx]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 20).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₄]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 24 := by
    rw [hsE, callEntry_esp', esp₄]; rfl
  have w₄ : s₄.wr = s.wr := u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))
  have r₄ : s₄.rd = s.rd := u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))
  have mE : s₄.mem = s.mem := u₄.mem.trans (u₃.mem.trans (u₂.mem.trans u₁.mem))
  have e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := VG.Proof.Argon2.X86.HPrime.setWidth_add (d := 192) (by omega)
  have e768 : (B + 768).setWidth 64 = B.setWidth 64 + 768 := VG.Proof.Argon2.X86.HPrime.setWidth_add (d := 768) (by omega)
  have stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right (Region.sub_prefix (by decide)))
  have scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  have dgR : (below E 60).Disjoint ⟨B.setWidth 64 + 768, 64⟩ := h.stk_sub (d := 768) (by decide) (Nat.le_refl _)
  have argSub : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩ (below E 60) :=
    below_sub (by decide) hlo
  have retSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 20) (by omega) hlo
    rw [show E - BitVec.ofNat 32 24 = E - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 24) (by omega) hlo
    have e : (E - BitVec.ofNat 32 24 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 24).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega)]; omega)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  have b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega
  have b768 : (B + 768).toNat = B.toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega
  refine WP.callWith (k := VG.Proof.Blake2.finalizeX86 b) VG.Proof.Argon2.X86.HPrime.finalize_correct VG.Proof.Argon2.X86.HPrime.finalize_nosp rs hrs
    (by rw [VG.Proof.Argon2.X86.HPrime.finalize_stack, esp₄]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨argAddr sE 0, 20⟩])
    (wr := [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩])
    ⟨?_, ?_, ?_⟩ fun t rd' wr' cs' f' ⟨s₃, m₃, post⟩ => ?_
  · rw [← hsE]
    simp only [VG.Proof.Blake2.finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, eA, eSp, e192, e768, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact stR.sub_left argSub
    · exact dgR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact dgR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact dgR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · omega
    · rw [b768]; omega
    · rw [b192]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := E.isLt; omega
  · rw [esp₄, w₄, r₄]
    refine Covers.append_left (Covers.cons (VG.Proof.Argon2.X86.HPrime.covers_frame eA _) Covers.nil)
      (VG.Proof.Argon2.X86.HPrime.covers_ins _ (Covers.right ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
        (h.cov (d := 192) (by decide))))))
  · rw [esp₄, w₄]
    exact VG.Proof.Argon2.X86.HPrime.covers_cons _ ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
      (h.cov (d := 192) (by decide))))
  · rw [VG.Proof.Argon2.X86.HPrime.finalize_stack, esp₄] at f'
    have hpush : Frame [below E 24] s₄.mem sE.mem := by
      have := callEntry_frame fit hrs; rw [esp₄] at this; exact this
    rw [← hsE] at post
    simp only [VG.Proof.Blake2.finalizeX86, arg_withRegions, State.withRegions_mem, a0, a3, e768, m₃] at post
    have reprE : Repr b h0 sE.mem (B.setWidth 64) d :=
      VG.Proof.Argon2.X86.HPrime.repr_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (stR.sub_left (below_sub (by decide) hlo)).symm) (mE ▸ repr)
    have countE : VG.Proof.Blake2.countX86 (sE.withRegions [⟨argAddr sE 0, 20⟩]
        [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩]) =
        BitVec.ofNat 64 d.length := by
      simp only [VG.Proof.Blake2.countX86, arg_withRegions, a1, a2]; exact hc
    refine ⟨post h0 d reprE hlen countE, fun r hr hne => (cs' r hr).trans ?_, rd'.trans r₄, wr'.trans w₄, ?_⟩
    · have : r ≠ .eax := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      exact o₄ r this hne
    · rw [← mE]
      exact f'.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) hlo⟩

end VG.Proof.Argon2.X86.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.HPrime.CallsCT`. -/
section

/-!
# Argon2 H′ on x86 (32-bit): the calls, in two runs

The macros calling the BLAKE2b functions leak the same trace in two runs that
pass them the same arguments (`init_rel`, `update_rel`, `finalize_rel`):
the instructions before each call are checked by the taint analysis, and the
call is related by the callee's constant time (`RelCT.callWith`), from the
callee's precondition in both runs (`init_pre`, `update_pre`,
`finalize_pre`). `rel_taint` and `rel_wp` add what each run satisfies by
correctness.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize initCode updateCode finalizeCode)
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-! ## Two runs -/

/-- Two runs, each described by `WP`, of code the taint analysis proves
constant time from the registers `rs` public. -/
theorem rel_taint {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τr rs) c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (τr rs) (fun s₁ s₂ h => agree_regs (hag s₁ s₂ h.1 h.2)) hc).wp
    fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- What each run satisfies, added to two runs that leak the same trace. -/
theorem rel_wp {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ :=
  (hct.wp fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A relation proved from facts of the related states. -/
theorem RelCT.of_pre {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa P c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂

/-- The callee's public data, `esp` and its first `n` arguments, agree in
two runs that agree on `esp` and on the registers pushed. -/
theorem call_pub {rs : List Reg} (hrs : Reg.esp ∉ rs) {s₁ s₂ : State}
    (fit : 4 * rs.length + 4 ≤ (s₁.gpr .esp).toNat) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (rd wr : List Region) :
    ((pushed rs s₁).callEntry.withRegions rd wr).gpr .esp =
      ((pushed rs s₂).callEntry.withRegions rd wr).gpr .esp ∧
    ∀ i < rs.length, VG.X86.arg ((pushed rs s₁).callEntry.withRegions rd wr) i =
      VG.X86.arg ((pushed rs s₂).callEntry.withRegions rd wr) i := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', hsp]
  · simp only [arg_withRegions]
    exact callEntry_arg_eq hrs fit hsp hr hi

/-! ## `init` -/

theorem init_pre {B E : BitVec 32} {s : State} (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {n : Nat}
    (hn : s.gpr .edx = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (ha : s.gpr .eax = 0)
    (hc : s.gpr .ecx = B) :
    CallPre (VG.Proof.Blake2.initX86 b) [.eax, .ecx, .edx, .ebx]
      [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩] [⟨B.setWidth 64, 192⟩] s := by
  have hrs : Reg.esp ∉ [Reg.eax, .ecx, .edx, .ebx] := by decide
  have esp₂ : s.gpr .esp = E := h.esp
  have fit : 4 * [Reg.eax, .ecx, .edx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₂]; have := h.lo; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .ecx, .edx, .ebx] s).callEntry with hsE
  have a0 : VG.X86.arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  have a1 : VG.X86.arg sE 1 = BitVec.ofNat 32 n := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hn]
  have a2 : VG.X86.arg sE 2 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hc]
  have a3 : VG.X86.arg sE 3 = 0 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have stR : Region.Sub ⟨B.setWidth 64, 192⟩ ⟨B.setWidth 64, 832⟩ := Region.sub_prefix (by decide)
  have d20 : (below E 20).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right stR).sub_left (below_sub (by decide) h.lo)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [VG.Proof.Blake2.initX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    have mb : (64 : Nat) ≤ b.maxBytes := by decide
    refine ⟨rfl, rfl, fun _ h₁ _ => by simp [Region.Contains] at h₁, ?_, ?_,
      by simp only [Proof.Blake2.bufOff, blockBytes]; have := h.fits; omega,
      by simp; have := B.isLt; omega, ?_, by simp [BitVec.toNat_ofNat]; omega,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega, by simp⟩
    · exact d20.sub_left (below_sub (by decide) (by have := h.lo; omega))
    · refine d20.sub_left ?_
      have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega) (by have := h.lo; omega)
      rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
        rw [← VG.Offset.sub_add_eq]; rfl]
      exact this
    · rw [sub_toNat (by have := h.lo; omega)]; have := E.isLt; omega
  · rw [esp₂]
    refine Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) ?_
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', hc'⟩ := h.wr a k ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains] at hc ⊢; omega⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    · exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
        ((h.wr.trans fun a k hi => let ⟨r', hr', hc'⟩ := hi
          InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)))
  · rw [esp₂]
    exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (h.wr.trans fun a k ⟨r', hr', hc'⟩ => ⟨r', List.mem_cons_of_mem _ hr', hc'⟩)

/-- What `init` needs: the state's context, and the digest length in `edx`. -/
def InitIn (B E : BitVec 32) (n : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.X86.HPrime.Ctx B E s ∧ s.gpr .edx = BitVec.ofNat 32 n

theorem init_rel {B E : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.HPrime.InitIn B E n s₁ ∧ VG.Proof.Argon2.X86.HPrime.InitIn B E n s₂) Impl.Argon2.X86.HPrime.init
      fun _ _ => True := by
  have blk : ∀ s, VG.Proof.Argon2.X86.HPrime.InitIn B E n s → WP isa (.block [.mov .eax (.imm 0), .mov .ecx (.reg .ebx)]) s
      fun t => VG.Proof.Argon2.X86.HPrime.Ctx B E t ∧ t.gpr .edx = BitVec.ofNat 32 n ∧ t.gpr .eax = 0 ∧ t.gpr .ecx = B :=
    fun s ⟨c, e⟩ => wp_movi fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
      ⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e],
       by rw [u₂.other _ (by decide), u₁.gpr],
       by rw [u₂.gpr, u₁.other _ (by decide), c.ebx]⟩
  unfold Impl.Argon2.X86.HPrime.init
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx, .edx] (fun s₁ s₂ ⟨c₁, e₁⟩ ⟨c₂, e₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [e₁, e₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := VG.Proof.Blake2.initX86 b) VG.Proof.Argon2.X86.HPrime.init_correct Proof.Blake2.X86.B.init_ct
    [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩] [⟨B.setWidth 64, 192⟩]
    fun s₁ s₂ ⟨⟨c₁, e₁, a₁, x₁⟩, ⟨c₂, e₂, a₂, x₂⟩⟩ => ?_
  have fit : 4 * [Reg.eax, .ecx, .edx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega
  have hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := VG.Proof.Argon2.X86.HPrime.call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [x₁, x₂]
    · rw [e₁, e₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
    [⟨B.setWidth 64, 192⟩]
  exact ⟨VG.Proof.Argon2.X86.HPrime.init_pre c₁ e₁ hn₁ hn₂ a₁ x₁, VG.Proof.Argon2.X86.HPrime.init_pre c₂ e₂ hn₁ hn₂ a₂ x₂, hsp, p₁, p₂⟩

/-! ## `update` -/

theorem update_pre {B E : BitVec 32} {s : State} (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .esi = D) (hL : (s.gpr .edi).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩) (ha : s.gpr .eax = B + 192) :
    CallPre (VG.Proof.Blake2.updateX86 b) [.eax, .edi, .esi, .edx, .ecx, .ebx]
      [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
      [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩] s := by
  have hrs : Reg.esp ∉ [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] := by decide
  have esp₂ : s.gpr .esp = E := h.esp
  have hlo := h.lo
  have fit : 4 * [Reg.eax, .edi, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₂]; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] s).callEntry with hsE
  have a0 : VG.X86.arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  have a3 : VG.X86.arg sE 3 = D := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hD]
  have a4 : (VG.X86.arg sE 4).toNat = L := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hL]
  have a5 : VG.X86.arg sE 5 = B + 192 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 28 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have hfit := h.fits
  have e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := VG.Proof.Argon2.X86.HPrime.setWidth_add (d := 192) (by omega)
  have stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    h.stk.sub_right (Region.sub_prefix (by decide))
  have scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  have stk60 : ∀ {k : Nat} {r : Region}, k ≤ 60 → (below E 60).Disjoint r → (below E k).Disjoint r :=
    fun hk d => d.sub_left (below_sub hk hlo)
  have retSub : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 24) (by omega) hlo
    rw [show E - BitVec.ofNat 32 28 = E - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 28) (by omega) hlo
    have e : (E - BitVec.ofNat 32 28 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 28).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega)]; omega)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  have argSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩ (below E 60) :=
    below_sub (by decide) hlo
  have b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [VG.Proof.Blake2.updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, a5, eA, eSp, e192, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact hDs.sub_right (Region.sub_prefix (by decide))
    · exact hDs.sub_right (Offset.sub_base _ (by decide))
    · exact stR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · exact hDk.sub_left calleeStk
    · omega
    · omega
    · rw [b192]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := E.isLt; omega
  · rw [esp₂]
    refine Covers.append_left (Covers.cons (VG.Proof.Argon2.X86.HPrime.covers_ins _ hDc) (Covers.cons (VG.Proof.Argon2.X86.HPrime.covers_frame rfl _)
      Covers.nil)) (VG.Proof.Argon2.X86.HPrime.covers_ins _ (Covers.right ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))))
  · rw [esp₂]
    exact VG.Proof.Argon2.X86.HPrime.covers_cons _ ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))

/-- What `update` needs: the state's context, the data at `D`, of `L` bytes,
and the count in `edx:ecx`. -/
def UpdateIn (B E D : BitVec 32) (L : Nat) (lo hi : BitVec 32) (s : State) : Prop :=
  VG.Proof.Argon2.X86.HPrime.Ctx B E s ∧ s.gpr .esi = D ∧ (s.gpr .edi).toNat = L ∧ s.gpr .ecx = lo ∧ s.gpr .edx = hi ∧
    Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr)

theorem update_rel {B E D : BitVec 32} {L : Nat} {lo hi : BitVec 32} (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.HPrime.UpdateIn B E D L lo hi s₁ ∧ VG.Proof.Argon2.X86.HPrime.UpdateIn B E D L lo hi s₂) VG.Impl.Argon2.X86.HPrime.update
      fun _ _ => True := by
  have blk : ∀ s, VG.Proof.Argon2.X86.HPrime.UpdateIn B E D L lo hi s →
      WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 192)]) s
      fun t => VG.Proof.Argon2.X86.HPrime.UpdateIn B E D L lo hi t ∧ t.gpr .eax = B + 192 :=
    fun s ⟨c, e1, e2, e3, e4, cv⟩ => wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil
      ⟨⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e1],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e2],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e3],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e4],
       by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact cv⟩,
       by rw [u₂.gpr, u₁.gpr, c.ebx]⟩
  unfold VG.Impl.Argon2.X86.HPrime.update
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx, .esi, .edi, .ecx, .edx]
    (fun s₁ s₂ ⟨c₁, d₁, l₁, x₁, y₁, _⟩ ⟨c₂, d₂, l₂, x₂, y₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [d₁, d₂]
      · exact BitVec.eq_of_toNat_eq (l₁.trans l₂.symm)
      · rw [x₁, x₂]
      · rw [y₁, y₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := VG.Proof.Blake2.updateX86 b) VG.Proof.Argon2.X86.HPrime.update_correct Proof.Blake2.X86.B.update_ct
    [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩]
    fun s₁ s₂ ⟨⟨⟨c₁, d₁, l₁, x₁, y₁, v₁⟩, a₁⟩, ⟨⟨c₂, d₂, l₂, x₂, y₂, v₂⟩, a₂⟩⟩ => ?_
  have fit : 4 * [Reg.eax, .edi, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega
  have hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := VG.Proof.Argon2.X86.HPrime.call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · exact BitVec.eq_of_toNat_eq (l₁.trans l₂.symm)
    · rw [d₁, d₂]
    · rw [y₁, y₂]
    · rw [x₁, x₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩]
  exact ⟨VG.Proof.Argon2.X86.HPrime.update_pre c₁ d₁ l₁ hDfit v₁ hDs hDk a₁, VG.Proof.Argon2.X86.HPrime.update_pre c₂ d₂ l₂ hDfit v₂ hDs hDk a₂, hsp, p₁, p₂⟩

/-! ## `finalize` -/

theorem finalize_pre {B E : BitVec 32} {s : State} (h : VG.Proof.Argon2.X86.HPrime.Ctx B E s) (ha : s.gpr .eax = B + 192)
    (hi : s.gpr .esi = B + 768) :
    CallPre (VG.Proof.Blake2.finalizeX86 b) [.eax, .esi, .edx, .ecx, .ebx] [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
      [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩] s := by
  have hrs : Reg.esp ∉ [Reg.eax, .esi, .edx, .ecx, .ebx] := by decide
  have esp₄ : s.gpr .esp = E := h.esp
  have hlo := h.lo
  have hfit := h.fits
  have fit : 4 * [Reg.eax, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₄]; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .esi, .edx, .ecx, .ebx] s).callEntry with hsE
  have a0 : VG.X86.arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  have a3 : VG.X86.arg sE 3 = B + 768 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hi]
  have a4 : VG.X86.arg sE 4 = B + 192 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 20).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₄]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 24 := by
    rw [hsE, callEntry_esp', esp₄]; rfl
  have e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := VG.Proof.Argon2.X86.HPrime.setWidth_add (d := 192) (by omega)
  have e768 : (B + 768).setWidth 64 = B.setWidth 64 + 768 := VG.Proof.Argon2.X86.HPrime.setWidth_add (d := 768) (by omega)
  have stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right (Region.sub_prefix (by decide)))
  have scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  have dgR : (below E 60).Disjoint ⟨B.setWidth 64 + 768, 64⟩ := h.stk_sub (d := 768) (by decide) (Nat.le_refl _)
  have argSub : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩ (below E 60) :=
    below_sub (by decide) hlo
  have retSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 20) (by omega) hlo
    rw [show E - BitVec.ofNat 32 24 = E - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 24) (by omega) hlo
    have e : (E - BitVec.ofNat 32 24 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 24).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega)]; omega)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  have b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega
  have b768 : (B + 768).toNat = B.toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [VG.Proof.Blake2.finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, eA, eSp, e192, e768, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact stR.sub_left argSub
    · exact dgR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact dgR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact dgR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · omega
    · rw [b768]; omega
    · rw [b192]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := E.isLt; omega
  · rw [esp₄]
    refine Covers.append_left (Covers.cons (VG.Proof.Argon2.X86.HPrime.covers_frame rfl _) Covers.nil)
      (VG.Proof.Argon2.X86.HPrime.covers_ins _ (Covers.right ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
        (h.cov (d := 192) (by decide))))))
  · rw [esp₄]
    exact VG.Proof.Argon2.X86.HPrime.covers_cons _ ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
      (h.cov (d := 192) (by decide))))

/-- What `finalize` needs: the state's context and the count in `edx:ecx`. -/
def FinalizeIn (B E lo hi : BitVec 32) (s : State) : Prop :=
  VG.Proof.Argon2.X86.HPrime.Ctx B E s ∧ s.gpr .ecx = lo ∧ s.gpr .edx = hi

theorem finalize_rel {B E lo hi : BitVec 32} :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.HPrime.FinalizeIn B E lo hi s₁ ∧ VG.Proof.Argon2.X86.HPrime.FinalizeIn B E lo hi s₂) VG.Impl.Argon2.X86.HPrime.finalize
      fun _ _ => True := by
  have blk : ∀ s, VG.Proof.Argon2.X86.HPrime.FinalizeIn B E lo hi s → WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 192),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm 768)]) s
      fun t => VG.Proof.Argon2.X86.HPrime.FinalizeIn B E lo hi t ∧ t.gpr .eax = B + 192 ∧ t.gpr .esi = B + 768 :=
    fun s ⟨c, e3, e4⟩ => wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
      WP.block_nil
      ⟨⟨c.of_regs (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide)])
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]),
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e3],
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e4]⟩,
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, c.ebx],
       by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.ebx]⟩
  unfold VG.Impl.Argon2.X86.HPrime.finalize
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx, .ecx, .edx]
    (fun s₁ s₂ ⟨c₁, x₁, y₁⟩ ⟨c₂, x₂, y₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [x₁, x₂]
      · rw [y₁, y₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := VG.Proof.Blake2.finalizeX86 b) VG.Proof.Argon2.X86.HPrime.finalize_correct Proof.Blake2.X86.B.finalize_ct
    [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩]
    fun s₁ s₂ ⟨⟨⟨c₁, x₁, y₁⟩, a₁, i₁⟩, ⟨⟨c₂, x₂, y₂⟩, a₂, i₂⟩⟩ => ?_
  have fit : 4 * [Reg.eax, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega
  have hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := VG.Proof.Argon2.X86.HPrime.call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [i₁, i₂]
    · rw [y₁, y₂]
    · rw [x₁, x₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩]
  exact ⟨VG.Proof.Argon2.X86.HPrime.finalize_pre c₁ a₁ i₁, VG.Proof.Argon2.X86.HPrime.finalize_pre c₂ a₂ i₂, hsp, p₁, p₂⟩

end VG.Proof.Argon2.X86.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.HPrime.Next`. -/
section

section

/-!
# Argon2 H′ on x86 (32-bit): hashing in `scratch`

What the hash macros keep (`Keeps`: `ebx`, `ebp`, `esp`, the permissions, and
the memory outside `scratch[0, 832)` and the stack below `esp`), and the hash of
a fixed `scratch` buffer (`absorbFixed_ok`) and of the 64-byte digest
(`next_ok`).
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed next)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-- What the hash macros keep. -/
structure Keeps (B E : BitVec 32) (s t : State) : Prop where
  ebx : t.gpr .ebx = s.gpr .ebx
  ebp : t.gpr .ebp = s.gpr .ebp
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨B.setWidth 64, 832⟩, below E 60] s.mem t.mem

theorem Keeps.refl {B E : BitVec 32} (s : State) : VG.Proof.Argon2.X86.HPrime.Keeps B E s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {B E : BitVec 32} {s t u : State} (h : VG.Proof.Argon2.X86.HPrime.Keeps B E s t) (h' : VG.Proof.Argon2.X86.HPrime.Keeps B E t u) :
    VG.Proof.Argon2.X86.HPrime.Keeps B E s u :=
  ⟨h'.ebx.trans h.ebx, h'.ebp.trans h.ebp, h'.esp.trans h.esp, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h.frame.trans h'.frame⟩

theorem Keeps.ctx {B E : BitVec 32} {s t : State} (h : VG.Proof.Argon2.X86.HPrime.Keeps B E s t) (c : VG.Proof.Argon2.X86.HPrime.Ctx B E s) : VG.Proof.Argon2.X86.HPrime.Ctx B E t :=
  c.of_regs h.ebx h.esp h.wr

/-- Calls keep the callee-saved registers and write within the regions. -/
theorem Keeps.of_call {B E : BitVec 32} {s t : State} (hr : ∀ r ∈ [Reg.ebx, .ebp, .esp], t.gpr r = s.gpr r)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [(⟨B.setWidth 64, 832⟩ : Region), below E 60], Region.Sub r r') :
    VG.Proof.Argon2.X86.HPrime.Keeps B E s t :=
  ⟨hr _ (by simp), hr _ (by simp), hr _ (by simp), hrd, hwr, hf.sub hs⟩

/-- The registers `Keeps` asks for are callee-saved. -/
theorem of_callee {s t : State} (h : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) :
    ∀ r ∈ [Reg.ebx, .ebp, .esp], t.gpr r = s.gpr r :=
  fun r hr => h r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)

/-- Bytes outside `scratch[0, 832)` and the stack are kept. -/
theorem Keeps.bytes {B E : BitVec 32} {s t : State} (h : VG.Proof.Argon2.X86.HPrime.Keeps B E s t) {R : Region}
    (hR : R.len ≤ 2 ^ 64) (h₁ : R.Disjoint ⟨B.setWidth 64, 832⟩) (h₂ : R.Disjoint (below E 60)) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len :=
  Proof.Blake2.bytesAt_congr fun i hi => h.frame.bytes (R := R) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂) hR hi

/-! ## Fixed buffers -/

/-- Absorb `size` bytes at `scratch + offset` into an empty state. -/
theorem absorbFixed_ok {B E : BitVec 32} {s : State} (c : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {offset size : Nat}
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hlo : 768 ≤ offset) (hs : 0 < size)
    (hcov : Covers [⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩] s.wr)
    (hstk : (below E 60).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩) {h0 : HashValue 64}
    (repr : Repr b h0 s.mem (B.setWidth 64) []) :
    WP isa (absorbFixed offset size) s fun t =>
      Repr b h0 t.mem (B.setWidth 64) (bytesAt s.mem (B.setWidth 64 + BitVec.ofNat 64 offset) size) ∧
      VG.Proof.Argon2.X86.HPrime.Keeps B E s t := by
  unfold absorbFixed
  have hfit := c.fits
  refine WP.seq (wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    wp_movi fun s₅ u₅ => WP.block_nil ?_)
  have o : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have m : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₅ : VG.Proof.Argon2.X86.HPrime.Ctx B E s₅ := c.of_regs (o _ (by decide) (by decide) (by decide) (by decide))
    (o _ (by decide) (by decide) (by decide) (by decide)) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have eD : s₅.gpr .esi = B + BitVec.ofNat 32 offset := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.ebx]
  have eDw : (B + BitVec.ofNat 32 offset).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 offset :=
    VG.Proof.Argon2.X86.HPrime.setWidth_add (by omega)
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]; omega
  have hL : (s₅.gpr .edi).toNat = size := by
    rw [u₅.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hDc : Covers [⟨(B + BitVec.ofNat 32 offset).setWidth 64, size⟩] (s₅.rd ++ s₅.wr) := by
    rw [eDw, show s₅.wr = s.wr by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]]; exact Covers.right hcov
  have hDs : Region.Disjoint ⟨(B + BitVec.ofNat 32 offset).setWidth 64, size⟩ ⟨B.setWidth 64, 768⟩ := by
    rw [eDw]; exact Offset.disjoint_base _ hlo (by omega)
  have hDk : (below E 60).Disjoint ⟨(B + BitVec.ofNat 32 offset).setWidth 64, size⟩ := by
    rw [eDw]; exact hstk
  have hcount : s₅.gpr .edx ++ s₅.gpr .ecx = BitVec.ofNat 64 ([] : List Byte).length := by
    have e1 : s₅.gpr .edx = 0 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    have e2 : s₅.gpr .ecx = 0 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]
    rw [e1, e2]; rfl
  refine (VG.Proof.Argon2.X86.HPrime.update_ok c₅ eD hL (by rw [dTo]; omega) hDc hDs hDk (by rw [m]; exact repr) hcount
    (by simp only [List.length_nil]; omega)).mono ?_
  rintro t ⟨r, cs, rd, wr, f⟩
  refine ⟨by rw [m, eDw, List.nil_append] at r; exact r, ?_⟩
  refine Keeps.of_call (fun q hq => (VG.Proof.Argon2.X86.HPrime.of_callee cs q hq).trans ?_) (rd.trans ?_) (wr.trans ?_) (m ▸ f) ?_
  · have : q ≠ .ecx ∧ q ≠ .edx ∧ q ≠ .esi ∧ q ≠ .edi := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    exact o q this.1 this.2.1 this.2.2.1 this.2.2.2
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the hash of the digest

`next_ok`: `next` replaces the 64-byte digest at `scratch + 768` with the
BLAKE2b hash of it, of the length in `edx`.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed next)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi)

theorem next_ok {B E : BitVec 32} {s : State} (c : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {n : Nat}
    (hn : s.gpr .edx = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa next s fun t =>
      bytesAt t.mem (B.setWidth 64 + 768) 64 =
        finalHash b (Spec.Blake2.init b n 0) (bytesAt s.mem (B.setWidth 64 + 768) 64) ∧
      VG.Proof.Argon2.X86.HPrime.Keeps B E s t := by
  unfold next
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.init_ok c hn hn₁ hn₂).mono fun s₁ ⟨r₁, cs₁, rd₁, wr₁, f₁⟩ => ?_)
  have k₁ : VG.Proof.Argon2.X86.HPrime.Keeps B E s s₁ := Keeps.of_call (VG.Proof.Argon2.X86.HPrime.of_callee cs₁) rd₁ wr₁ f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩
  have dg : bytesAt s₁.mem (B.setWidth 64 + 768) 64 = bytesAt s.mem (B.setWidth 64 + 768) 64 := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f₁.bytes (R := ⟨B.setWidth 64 + 768, 64⟩) ?_ (by simp) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · exact (c.stk_sub (d := 768) (n := 64) (by decide) (by decide)).symm
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.absorbFixed_ok (k₁.ctx c) (offset := 768) (size := 64) (by have := c.fits; omega) (by decide) (by decide)
    ((k₁.ctx c).cov (by decide)) (c.stk_sub (by decide) (by decide)) r₁).mono
    fun s₂ ⟨r₂, k₂⟩ => ?_)
  rw [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, dg] at r₂
  have c₂ := (k₁.trans k₂).ctx c
  refine WP.seq (wp_movi fun s₃ u₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_)
  have c₄ : VG.Proof.Argon2.X86.HPrime.Ctx B E s₄ := c₂.of_regs (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine (VG.Proof.Argon2.X86.HPrime.finalize_ok c₄ (d := bytesAt s.mem (B.setWidth 64 + 768) 64) (by rw [m₄]; exact r₂)
    (by
      have len : (bytesAt s.mem (B.setWidth 64 + 768) 64).length = 64 := by simp [bytesAt]
      rw [u₄.gpr, u₄.other _ (by decide), u₃.gpr, len]; rfl) (by simp [bytesAt])).mono ?_
  rintro t ⟨d, cs, rd, wr, f⟩
  refine ⟨d, (k₁.trans k₂).trans ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cs _ (by decide) (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
  · rw [cs _ (by decide) (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
  · rw [cs _ (by decide) (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
  · rw [rd, u₄.rd, u₃.rd]
  · rw [wr, u₄.wr, u₃.wr]
  · rw [← m₄]; exact f

end VG.Proof.Argon2.X86.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.HPrime.Output`. -/
section

section

/-!
# Argon2 H′ on x86 (32-bit): the state of the body

`Body s₀ s`: between H′'s setup and its restore, `ebx` points to `scratch`,
`esp` is as on entry, memory has changed only in the output, `scratch` and
the stack below `esp`, and the caller's registers and the length prefix are
kept in `scratch`. `Out s₀ s k`: the output pointer and the bytes left, after
`k` output bytes. `copy_ok`: copying digest bytes to the output.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy outOff leftOff saved)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_addi wp_movm wp_store contains_addr)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

/-- The state of the body. -/
structure Body (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = VG.Proof.Argon2.X86.HPrime.scr s₀
  esp : s.gpr .esp = VG.Proof.Argon2.X86.HPrime.esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Argon2.X86.HPrime.outR s₀, VG.Proof.Argon2.X86.HPrime.scrR s₀, VG.Proof.Argon2.X86.HPrime.stkR s₀] s₀.mem s.mem
  saved : ∀ p ∈ saved, s.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) p.2) 32 = s₀.gpr p.1
  pfx : bytesAt s.mem (VG.Proof.Argon2.X86.HPrime.P s₀ + 832) 4 = Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀)
include hp

theorem Body.ctx {s : State} (h : VG.Proof.Argon2.X86.HPrime.Body s₀ s) : VG.Proof.Argon2.X86.HPrime.Ctx (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s :=
  ⟨h.ebx, h.esp, by have := hp.scr_fits; omega, hp.esp_lo, by have := hp.esp_hi; omega,
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [h.wr, hp.wr], 0, by simp, by simp⟩),
    hp.stk_scr.sub_right (Region.sub_prefix (by decide))⟩

/-- A word of `scratch` from offset 832 on is kept by the hash macros. -/
theorem keeps_word {s t : State} (k : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t) {d : Nat} (hd : 832 ≤ d)
    (hd' : d + 4 ≤ 16384) : t.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 = s.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 := by
  refine k.frame.readW (r := ⟨addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  have e := VG.Proof.Argon2.X86.HPrime.scr_addr hp (d := d) (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [e]; exact Offset.disjoint_base _ hd (by omega)
  · rw [e]
    exact (hp.stk_scr.sub_right (Offset.sub_base _ (show d + 4 ≤ 16384 from hd'))).symm

theorem Body.keeps {s t : State} (h : VG.Proof.Argon2.X86.HPrime.Body s₀ s) (k : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t) : VG.Proof.Argon2.X86.HPrime.Body s₀ t := by
  refine ⟨k.ebx.trans h.ebx, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (k.frame.sub fun r hr => ?_), fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.Argon2.X86.HPrime.stkR s₀, by simp, fun _ h => h⟩
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ 16384 := by
      simp only [Impl.Argon2.X86.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [VG.Proof.Argon2.X86.HPrime.keeps_word hp k hb.1 hb.2]; exact h.saved q hq
  · rw [← h.pfx]
    exact k.bytes (R := ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + 832, 4⟩) (by simp) (Offset.disjoint_base _ (by decide) (by decide))
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))).symm

end

/-! ## Copying digest bytes -/

/-- The output pointer after `k` output bytes. -/
def OutPtr (s₀ s : State) (k : Nat) : Prop :=
  s.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) outOff) 32 = VG.Proof.Argon2.X86.HPrime.op s₀ + BitVec.ofNat 32 k

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀)
include hp

theorem copy_ok {s : State} (h : VG.Proof.Argon2.X86.HPrime.Body s₀ s) {k n : Nat} (hk : VG.Proof.Argon2.X86.HPrime.OutPtr s₀ s k)
    (hn : s.gpr .esi = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : k + n ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) :
    WP isa copy s fun t => VG.Proof.Argon2.X86.HPrime.Body s₀ t ∧ VG.Proof.Argon2.X86.HPrime.OutPtr s₀ t (k + n) ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k) n = bytesAt s.mem (VG.Proof.Argon2.X86.HPrime.P s₀ + 768) n ∧
      t.gpr .ebp = s.gpr .ebp ∧
      Frame [⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 outOff, 4⟩]
        s.mem t.mem := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  unfold copy
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movm
    (VG.Proof.Sha512.X86.ea_of (B := VG.Proof.Argon2.X86.HPrime.scr s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebx])
      outOff)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]
        exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₃ u₃ => WP.block_nil ?_)
  have mem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have edx₃ : s₃.gpr .edx = VG.Proof.Argon2.X86.HPrime.scr s₀ + 768 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.ebx]
  have edi₃ : s₃.gpr .edi = VG.Proof.Argon2.X86.HPrime.op s₀ + BitVec.ofNat 32 k := by
    rw [u₃.gpr, u₂.mem, u₁.mem]; exact hk
  have esi₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hn]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  have e768 : (VG.Proof.Argon2.X86.HPrime.scr s₀ + 768).setWidth 64 = VG.Proof.Argon2.X86.HPrime.P s₀ + 768 := VG.Proof.Argon2.X86.HPrime.setWidth_add (d := 768) (by omega)
  have b768 : (VG.Proof.Argon2.X86.HPrime.scr s₀ + 768).toNat = (VG.Proof.Argon2.X86.HPrime.scr s₀).toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega
  have bk : (VG.Proof.Argon2.X86.HPrime.op s₀ + BitVec.ofNat 32 k).toNat = (VG.Proof.Argon2.X86.HPrime.op s₀).toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]; omega
  have eOut : addr (VG.Proof.Argon2.X86.HPrime.op s₀ + BitVec.ofNat 32 k) 0 = (VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k := by
    rw [MdStream.X86.addr_add_ofNat (by omega), Nat.add_zero]
  refine WP.seq (Proof.Blake2.X86.Stream.copyLoop_ok (w := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (k := n) hn₁ (by omega) (by rw [b768]; omega)
    (by simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero]; rw [bk]; omega)
    edx₃ edi₃ esi₃ (fun i hi => ?_) (fun i hi => ?_) ?_ fun t ht => ?_)
  · have : i < 64 := by omega
    rw [rd₃, wr₃, e768, show VG.Proof.Argon2.X86.HPrime.P s₀ + 768 + BitVec.ofNat 64 i = VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 (768 + i) by
      rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
    refine ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], ?_⟩
    exact Offset.contains_base _ (d := 768 + i) (n := 1) (k := 16384) (by omega) (by omega)
  · rw [wr₃]
    simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, eOut]
    refine ⟨VG.Proof.Argon2.X86.HPrime.outR s₀, by simp [hp.wr], ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (d := k + i) (n := 1) (k := VG.Proof.Argon2.X86.HPrime.ol s₀) (by omega) (by omega)
  · rw [e768]
    simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, eOut]
    exact (hp.out_scr.sub_left (Offset.sub_base _ (d := k) (n := n) (k := VG.Proof.Argon2.X86.HPrime.ol s₀) (by omega))).sub_right
      (Offset.sub_base (VG.Proof.Argon2.X86.HPrime.P s₀) (d := 768) (n := n) (k := 16384) (by omega)) |>.symm
  -- The store of the output pointer.
  have o : ∀ x, x ≠ .edx → x ≠ .edi → x ≠ .esi → x ≠ .eax → t.gpr x = s.gpr x := fun x a b c d => by
    rw [ht.other x a b c d, u₃.other _ b, u₂.other _ a, u₁.other _ a]
  have ebxT : t.gpr .ebx = VG.Proof.Argon2.X86.HPrime.scr s₀ := by rw [o _ (by decide) (by decide) (by decide) (by decide), h.ebx]
  have wrT : t.wr = s₀.wr := ht.wr.trans wr₃
  have dstE : addr (VG.Proof.Argon2.X86.HPrime.op s₀ + BitVec.ofNat 32 k) (Proof.Blake2.bufOff 0) =
      (VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k := eOut
  have lenL : (bytesAt s.mem (VG.Proof.Argon2.X86.HPrime.P s₀ + 768) n).length = n := by simp [bytesAt]
  have memT : t.mem = VG.WriteBytes.writeBytes s.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k)
      (bytesAt s.mem (VG.Proof.Argon2.X86.HPrime.P s₀ + 768) n) := by
    rw [ht.mem, dstE, e768, mem₃, List.take_of_length_le (by rw [lenL])]
  refine wp_store (VG.Proof.Sha512.X86.ea_of ebxT outOff)
    (by rw [wrT]; exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun t' u => WP.block_nil ?_
  have eslot : addr (VG.Proof.Argon2.X86.HPrime.scr s₀) outOff = VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 outOff := VG.Proof.Argon2.X86.HPrime.scr_addr hp (by decide)
  have F : Frame [⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 outOff, 4⟩]
      s.mem t'.mem := by
    rw [u.mem, memT, eslot]
    refine ((VG.WriteBytes.writeBytes_frame s.mem _ _ (R := ⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩)
      (by rw [lenL]; exact Region.contains_self _ _)).mono (by simp)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have outSub : Region.Sub ⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩ (VG.Proof.Argon2.X86.HPrime.outR s₀) :=
    Offset.sub_base _ (by omega)
  have slotSub : Region.Sub ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 outOff, 4⟩ (VG.Proof.Argon2.X86.HPrime.scrR s₀) :=
    Offset.sub_base _ (by decide)
  have keep : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ outOff ∨ outOff + 4 ≤ d) →
      t'.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 = s.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 := fun d hd hd' => by
    refine F.readW (r := ⟨addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    rw [VG.Proof.Argon2.X86.HPrime.scr_addr hp (by omega)]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ hd)).symm
    · exact Offset.disjoint _ hd' (by omega) (by simp only [outOff]; omega)
  refine ⟨⟨by rw [u.gpr, ebxT], by rw [u.gpr, o _ (by decide) (by decide) (by decide) (by decide), h.esp],
      by rw [u.rd, ht.rd, rd₃], by rw [u.wr, wrT], ?_, fun q hq => ?_, ?_⟩, ?_, ?_,
    by rw [u.gpr, o _ (by decide) (by decide) (by decide) (by decide)], F⟩
  · exact h.frame.trans (F.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.Argon2.X86.HPrime.outR s₀, by simp, outSub⟩
      · exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp, slotSub⟩)
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ outOff := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keep _ (by simp only [outOff] at hb; omega) (.inl hb.2)]; exact h.saved q hq
  · rw [← h.pfx]
    refine Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + 832, 4⟩) (fun r hr => ?_)
      (by simp) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left outSub).sub_right
        (Offset.sub_base (VG.Proof.Argon2.X86.HPrime.P s₀) (d := 832) (n := 4) (k := 16384) (by decide))).symm
    · exact Offset.disjoint (VG.Proof.Argon2.X86.HPrime.P s₀) (d := 832) (n := 4) (e := outOff) (k := 4) (by decide) (by decide)
        (by decide)
  · show _ = _
    rw [u.mem, Mem.readW_writeW_self32, ht.dstV, BitVec.add_assoc, BitVec.ofNat_add]
  · have wb : bytesAt t.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k) n = bytesAt s.mem (VG.Proof.Argon2.X86.HPrime.P s₀ + 768) n := by
      rw [memT]
      have := VG.Proof.Argon2.X86.HPrime.bytesAt_writeBytes s.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k)
        (bytesAt s.mem (VG.Proof.Argon2.X86.HPrime.P s₀ + 768) n) (by rw [lenL]; omega)
      rwa [lenL] at this
    rw [← wb, u.mem]
    refine Proof.Blake2.bytesAt_congr fun i hi =>
      ((Frame.refl [⟨addr (VG.Proof.Argon2.X86.HPrime.scr s₀) outOff, 4⟩] t.mem).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)).bytes (R := ⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩) ?_ (by simp; omega) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [eslot]
    exact (hp.out_scr.sub_left outSub).sub_right slotSub

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the output

`Out s₀ s xs`: the output so far, `xs`, its pointer and the bytes left.
`emit_ok` writes a 32-byte prefix of the digest, `copyRemaining_ok` the last
bytes.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy outOff leftOff emitPrefix copyRemaining)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_movm wp_store wp_subi contains_addr)

/-- The output so far. -/
structure Out (s₀ s : State) (xs : List Byte) : Prop where
  ptr : VG.Proof.Argon2.X86.HPrime.OutPtr s₀ s xs.length
  left : s.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 32 = BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length)
  bytes : bytesAt s.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64) xs.length = xs
  len : xs.length ≤ VG.Proof.Argon2.X86.HPrime.ol s₀

/-- The digest. -/
abbrev digest (s₀ s : State) : List Byte := bytesAt s.mem (VG.Proof.Argon2.X86.HPrime.P s₀ + 768) 64

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀)
include hp

/-- The output and its slots are kept by the hash macros. -/
theorem Out.keeps {s t : State} {xs : List Byte} (h : VG.Proof.Argon2.X86.HPrime.Out s₀ s xs)
    (k : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t) : VG.Proof.Argon2.X86.HPrime.Out s₀ t xs := by
  refine ⟨?_, ?_, ?_, h.len⟩
  · show _ = _; rw [VG.Proof.Argon2.X86.HPrime.keeps_word hp k (by decide) (by decide)]; exact h.ptr
  · rw [VG.Proof.Argon2.X86.HPrime.keeps_word hp k (by decide) (by decide)]; exact h.left
  · have kb := k.bytes (R := ⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64, xs.length⟩)
      (by have := h.len; have := hp.out_fits; simp; omega)
      ((hp.out_scr.sub_left (Region.sub_prefix h.len)).sub_right (Region.sub_prefix (by decide)))
      ((hp.stk_out.sub_right (Region.sub_prefix h.len)).symm)
    simp only at kb
    rw [kb]; exact h.bytes

/-- A word of `scratch` outside the output pointer's slot is kept by `copy`. -/
theorem copy_word {s t : State} {k n : Nat} (hkn : k + n ≤ VG.Proof.Argon2.X86.HPrime.ol s₀)
    (f : Frame [⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 outOff, 4⟩]
      s.mem t.mem) {d : Nat} (hd : d + 4 ≤ 16384) (hd' : d + 4 ≤ outOff ∨ outOff + 4 ≤ d) :
    t.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 = s.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 := by
  have ho := hp.out_fits
  refine f.readW (r := ⟨addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  rw [VG.Proof.Argon2.X86.HPrime.scr_addr hp (by omega)]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ((hp.out_scr.sub_left (Offset.sub_base _ (by omega))).sub_right
      (Offset.sub_base _ hd)).symm
  · exact Offset.disjoint _ hd' (by omega) (by simp only [outOff]; omega)

/-- Emit `n` digest bytes after the output `xs`. -/
theorem copyOut_ok {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) {xs : List Byte} (h : VG.Proof.Argon2.X86.HPrime.Out s₀ s xs) {n : Nat}
    (hn : s.gpr .esi = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : xs.length + n ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) :
    WP isa copy s fun t => VG.Proof.Argon2.X86.HPrime.Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64) (xs.length + n) = xs ++ (VG.Proof.Argon2.X86.HPrime.digest s₀ s).take n ∧
      VG.Proof.Argon2.X86.HPrime.OutPtr s₀ t (xs.length + n) ∧
      t.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 32 = s.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 32 ∧
      VG.Proof.Argon2.X86.HPrime.digest s₀ t = VG.Proof.Argon2.X86.HPrime.digest s₀ s := by
  have ho := hp.out_fits
  refine (VG.Proof.Argon2.X86.HPrime.copy_ok hp b h.ptr hn hn₁ hn₂ hkn).mono ?_
  rintro t ⟨bt, pt, bytes, ebp, f⟩
  refine ⟨bt, ebp, ?_, pt, VG.Proof.Argon2.X86.HPrime.copy_word hp hkn f (by decide) (by decide), ?_⟩
  swap
  · refine Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + 768, 64⟩) (fun r hr => ?_)
      (by simp) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left (Offset.sub_base _ (d := xs.length) (n := n) (k := VG.Proof.Argon2.X86.HPrime.ol s₀) (by omega))).sub_right
        (Offset.sub_base (VG.Proof.Argon2.X86.HPrime.P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
    · exact Offset.disjoint (VG.Proof.Argon2.X86.HPrime.P s₀) (d := 768) (n := 64) (e := outOff) (k := 4) (by decide) (by decide)
        (by decide)
  have old : bytesAt t.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64) xs.length = bytesAt s.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64) xs.length := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := ⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64, xs.length⟩)
      (fun r hr => ?_) (by have := h.len; simp; omega) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.base_disjoint _ (by omega) (by omega)
    · exact (hp.out_scr.sub_left (Region.sub_prefix (by omega))).sub_right
        (Offset.sub_base _ (by decide))
  rw [Proof.Blake2.bytesAt_add, bytes, VG.Proof.Argon2.X86.HPrime.bytesAt_take _ _ _ _ hn₂, old, h.bytes]

/-- Emit a 32-byte prefix of the digest. -/
theorem emit_ok {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) {xs : List Byte} (h : VG.Proof.Argon2.X86.HPrime.Out s₀ s xs)
    (hkn : xs.length + 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) :
    WP isa emitPrefix s fun t => VG.Proof.Argon2.X86.HPrime.Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      VG.Proof.Argon2.X86.HPrime.Out s₀ t (xs ++ (VG.Proof.Argon2.X86.HPrime.digest s₀ s).take 32) ∧ VG.Proof.Argon2.X86.HPrime.digest s₀ t = VG.Proof.Argon2.X86.HPrime.digest s₀ s := by
  have ho := hp.out_fits
  have hs := hp.scr_fits
  unfold emitPrefix
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have b₁ : VG.Proof.Argon2.X86.HPrime.Body s₀ s₁ := ⟨by rw [u₁.other _ (by decide), b.ebx], by rw [u₁.other _ (by decide), b.esp],
    by rw [u₁.rd, b.rd], by rw [u₁.wr, b.wr], by rw [u₁.mem]; exact b.frame,
    fun q hq => by rw [u₁.mem]; exact b.saved q hq, by rw [u₁.mem]; exact b.pfx⟩
  have h₁ : VG.Proof.Argon2.X86.HPrime.Out s₀ s₁ xs := ⟨by show _ = _; rw [u₁.mem]; exact h.ptr, by rw [u₁.mem]; exact h.left,
    by rw [u₁.mem]; exact h.bytes, h.len⟩
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.copyOut_ok hp b₁ h₁ u₁.gpr (by decide) (by decide) hkn).mono
    fun s₂ ⟨b₂, e₂, by₂, p₂, l₂, d₂⟩ => ?_)
  have rl : InRegions (s₂.rd ++ s₂.wr) (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 4 := by
    rw [b₂.rd, b₂.wr]; exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b₂.ebx leftOff) rl fun s₃ u₃ => wp_subi fun s₄ u₄ _ => ?_
  have ebx₄ : s₄.gpr .ebx = VG.Proof.Argon2.X86.HPrime.scr s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), b₂.ebx]
  have wl : InRegions s₄.wr (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 4 := by
    rw [u₄.wr, u₃.wr, b₂.wr]; exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine wp_store (VG.Proof.Sha512.X86.ea_of ebx₄ leftOff) wl fun s₅ u₅ => WP.block_nil ?_
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have d₁ : VG.Proof.Argon2.X86.HPrime.digest s₀ s₁ = VG.Proof.Argon2.X86.HPrime.digest s₀ s := by simp only [VG.Proof.Argon2.X86.HPrime.digest, u₁.mem]
  have v₄ : s₄.gpr .eax = BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.ol s₀ - (xs.length + 32)) := by
    rw [u₄.gpr, u₃.gpr, l₂, u₁.mem, h.left]
    exact (Proof.Sha256.X86.Stream.sub_ofNat (a := VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length) (b := 32) (by omega)).trans
      (by congr 1)
  have e₅ : s₅.mem = s₂.mem.writeW (VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 leftOff) (BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.ol s₀ - (xs.length + 32))) := by
    rw [u₅.mem, m₄, v₄, VG.Proof.Argon2.X86.HPrime.scr_addr hp (by decide)]
  have F : Frame [⟨VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 leftOff, 4⟩] s₂.mem s₅.mem := by
    rw [e₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have keepW : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ leftOff ∨ leftOff + 4 ≤ d) →
      s₅.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 = s₂.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 := fun d hd hd' => by
    rw [e₅, VG.Proof.Argon2.X86.HPrime.scr_addr hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ hd' (by omega) (by simp only [leftOff]; omega)) (by decide)
  have keepB : ∀ R : Region, R.len ≤ 2 ^ 64 → R.Disjoint ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 leftOff, 4⟩ →
      bytesAt s₅.mem R.base R.len = bytesAt s₂.mem R.base R.len := fun R hR hd =>
    Proof.Blake2.bytesAt_congr fun i hi => F.bytes (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) hR hi
  have slotScr : Region.Sub ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 leftOff, 4⟩ (VG.Proof.Argon2.X86.HPrime.scrR s₀) := Offset.sub_base _ (by decide)
  have len' : (xs ++ (VG.Proof.Argon2.X86.HPrime.digest s₀ s).take 32).length = xs.length + 32 := by
    simp [VG.Proof.Argon2.X86.HPrime.digest, bytesAt]
  refine ⟨⟨by rw [u₅.gpr, ebx₄], by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), b₂.esp],
      by rw [u₅.rd, u₄.rd, u₃.rd, b₂.rd], by rw [u₅.wr, u₄.wr, u₃.wr, b₂.wr],
      b₂.frame.trans (F.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp, slotScr⟩),
      fun q hq => ?_, ?_⟩,
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), e₂, u₁.other _ (by decide)], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ leftOff := by
      simp only [Impl.Argon2.X86.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keepW _ (by simp only [leftOff] at hb; omega) (.inl hb.2)]; exact b₂.saved q hq
  · rw [keepB ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + 832, 4⟩ (by simp) (Offset.disjoint (VG.Proof.Argon2.X86.HPrime.P s₀) (d := 832) (n := 4) (e := leftOff) (k := 4)
      (by decide) (by decide) (by decide))]
    exact b₂.pfx
  · show _ = _
    rw [len', keepW _ (by decide) (by decide)]; exact p₂
  · rw [len', e₅, VG.Proof.Argon2.X86.HPrime.scr_addr hp (by decide), Mem.readW_writeW_self32]
  · rw [len']
    have k₁ := keepB ⟨(VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64, xs.length + 32⟩ (by simp; omega)
      ((hp.out_scr.sub_left (Region.sub_prefix (by omega))).sub_right slotScr)
    simp only at k₁
    rw [k₁, by₂, d₁]
  · rw [len']; exact hkn
  · have k₂ := keepB ⟨VG.Proof.Argon2.X86.HPrime.P s₀ + 768, 64⟩ (by simp) (Offset.disjoint (VG.Proof.Argon2.X86.HPrime.P s₀) (d := 768) (n := 64)
      (e := leftOff) (k := 4) (by decide) (by decide) (by decide))
    simp only at k₂
    show bytesAt _ _ _ = bytesAt _ _ _
    rw [k₂]; exact d₂.trans d₁

/-- Copy the bytes left. -/
theorem copyRemaining_ok {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) {xs : List Byte} (h : VG.Proof.Argon2.X86.HPrime.Out s₀ s xs)
    (hn₁ : xs.length < VG.Proof.Argon2.X86.HPrime.ol s₀) (hn₂ : VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length ≤ 64) :
    WP isa copyRemaining s fun t => VG.Proof.Argon2.X86.HPrime.Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64) (VG.Proof.Argon2.X86.HPrime.ol s₀) = xs ++ (VG.Proof.Argon2.X86.HPrime.digest s₀ s).take (VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length) := by
  have hs := hp.scr_fits
  unfold copyRemaining
  have rl : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]; exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ => WP.block_nil ?_)
  have b₁ : VG.Proof.Argon2.X86.HPrime.Body s₀ s₁ := ⟨by rw [u₁.other _ (by decide), b.ebx], by rw [u₁.other _ (by decide), b.esp],
    by rw [u₁.rd, b.rd], by rw [u₁.wr, b.wr], by rw [u₁.mem]; exact b.frame,
    fun q hq => by rw [u₁.mem]; exact b.saved q hq, by rw [u₁.mem]; exact b.pfx⟩
  have h₁ : VG.Proof.Argon2.X86.HPrime.Out s₀ s₁ xs := ⟨by show _ = _; rw [u₁.mem]; exact h.ptr, by rw [u₁.mem]; exact h.left,
    by rw [u₁.mem]; exact h.bytes, h.len⟩
  refine (VG.Proof.Argon2.X86.HPrime.copyOut_ok hp b₁ h₁ (n := VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length) (by rw [u₁.gpr, h.left]) (by omega) hn₂
    (by omega)).mono fun t ⟨bt, et, byt, _, _, _⟩ => ⟨bt, by rw [et, u₁.other _ (by decide)], ?_⟩
  rw [show xs.length + (VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length) = VG.Proof.Argon2.X86.HPrime.ol s₀ by omega] at byt
  rw [byt]; simp only [VG.Proof.Argon2.X86.HPrime.digest, u₁.mem]

end

end VG.Proof.Argon2.X86.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.HPrime.Finish`. -/
section

section

section

/-!
# Argon2 H′ on x86 (32-bit): the first digest

`first_ok`: `first` leaves H(min(out_len, 64), LE32(out_len) ‖ input) at the
start of the digest, `scratch[768, 832)`. The input is read before anything
is written to the output, so the two may overlap.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed chooseLength absorbInput finishInput
  first leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_movi wp_movm wp_cmpi)
open VG.Proof.Blake2.X86.CompressB (wp_addC wp_adcC)
open VG.Impl.Sha512.X86 (at_)

/-- Steps that keep memory, the permissions, `ebx`, `ebp` and `esp`. -/
theorem Keeps.same {B E : BitVec 32} {s t : State} (hb : t.gpr .ebx = s.gpr .ebx)
    (hp : t.gpr .ebp = s.gpr .ebp) (hs : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : VG.Proof.Argon2.X86.HPrime.Keeps B E s t :=
  ⟨hb, hp, hs, hrd, hwr, hm ▸ Frame.refl _ _⟩

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀)
include hp

theorem arg_addr {i : Nat} (hi : i < 5) :
    addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * i) = (VG.Proof.Argon2.X86.HPrime.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_eq (by have := hp.esp_hi; omega)

theorem arg_sub {i : Nat} (hi : i < 5) : Region.Sub ⟨addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * i), 4⟩ (VG.Proof.Argon2.X86.HPrime.argR s₀) := by
  show Region.Sub _ ⟨addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * 0), 20⟩
  rw [VG.Proof.Argon2.X86.HPrime.arg_addr hp hi, VG.Proof.Argon2.X86.HPrime.arg_addr hp (by decide)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are kept in the body. -/
theorem Body.arg {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * i)) 32 = VG.X86.arg s₀ i := by
  have he := hp.esp_hi
  have hl := hp.esp_lo
  refine b.frame.readW (r := ⟨addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.arg_out.sub_left (VG.Proof.Argon2.X86.HPrime.arg_sub hp hi)
  · exact hp.arg_scr.sub_left (VG.Proof.Argon2.X86.HPrime.arg_sub hp hi)
  · show Region.Disjoint _ ⟨(VG.Proof.Argon2.X86.HPrime.esp₀ s₀ - BitVec.ofNat 32 60).setWidth 64, 60⟩
    rw [VG.Proof.Argon2.X86.HPrime.arg_addr hp hi, Taint.sub_setWidth hl]
    exact Offset.disjoint_below _ (by omega)

theorem Body.arg_in {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * i)) 4 := by
  refine ⟨VG.Proof.Argon2.X86.HPrime.argR s₀, by simp [b.rd, hp.rd], ?_⟩
  show Region.Contains ⟨addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * 0), 20⟩ _ _
  rw [VG.Proof.Argon2.X86.HPrime.arg_addr hp hi, VG.Proof.Argon2.X86.HPrime.arg_addr hp (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

omit hp in
theorem Out.same {s t : State} {xs : List Byte} (h : VG.Proof.Argon2.X86.HPrime.Out s₀ s xs) (hm : t.mem = s.mem) : VG.Proof.Argon2.X86.HPrime.Out s₀ t xs :=
  ⟨by show _ = _; rw [hm]; exact h.ptr, by rw [hm]; exact h.left, by rw [hm]; exact h.bytes, h.len⟩

/-- `edx := min(out_len, 64)`. -/
theorem choose_ok {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) (o : VG.Proof.Argon2.X86.HPrime.Out s₀ s []) :
    WP isa chooseLength s fun t => t.gpr .edx = BitVec.ofNat 32 (min (VG.Proof.Argon2.X86.HPrime.ol s₀) 64) ∧
      VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t := by
  have hs := hp.scr_fits
  have hol := (VG.X86.arg s₀ 3).isLt
  unfold chooseLength
  have rl : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]
    exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ?_)
  have e₁ : s₁.gpr .edx = BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.ol s₀) := by rw [u₁.gpr, o.left]; rfl
  have k₂ : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s s₂ := Keeps.same
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd])
    (by rw [f₂.wr, u₁.wr])
  refine WP.ite (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ < 65)) (by
      show s₂.cf = _
      rw [cf₂, e₁, Proof.Sha256.X86.Stream.toNat_ofNat_lt hol]; rfl)
    (fun h => WP.block_nil ⟨?_, k₂⟩) (fun h => wp_movi fun s₃ u₃ => WP.block_nil ⟨?_, ?_⟩)
  · have : VG.Proof.Argon2.X86.HPrime.ol s₀ ≤ 64 := by simp only [decide_eq_true_eq] at h; omega
    rw [f₂.gpr, e₁, Nat.min_eq_left this]
  · have : 64 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ := by simp only [decide_eq_false_iff_not] at h; omega
    rw [u₃.gpr, Nat.min_eq_right this]; rfl
  · exact k₂.trans (Keeps.same (u₃.other _ (by decide)) (u₃.other _ (by decide)) (u₃.other _ (by decide))
      u₃.mem u₃.rd u₃.wr)

end

/-! ## The steps of `first` -/

/-- The state before and between the steps of `first`: the body, no output
yet, `ebp` and the input kept. -/
structure F0 (s₀ s : State) : Prop where
  body : VG.Proof.Argon2.X86.HPrime.Body s₀ s
  out : VG.Proof.Argon2.X86.HPrime.Out s₀ s []
  ebp : s.gpr .ebp = s₀.gpr .ebp
  input : bytesAt s.mem ((VG.Proof.Argon2.X86.HPrime.inp s₀).setWidth 64) (VG.Proof.Argon2.X86.HPrime.inl s₀) = bytesAt s₀.mem ((VG.Proof.Argon2.X86.HPrime.inp s₀).setWidth 64) (VG.Proof.Argon2.X86.HPrime.inl s₀)

/-- The length of the first digest. -/
abbrev nF (s₀ : State) : Nat := min (VG.Proof.Argon2.X86.HPrime.ol s₀) 64

/-- The input, on entry. -/
abbrev inB (s₀ : State) : List Byte := bytesAt s₀.mem ((VG.Proof.Argon2.X86.HPrime.inp s₀).setWidth 64) (VG.Proof.Argon2.X86.HPrime.inl s₀)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀)
include hp

theorem F0.keeps {s t : State} (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s) (k : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t) : VG.Proof.Argon2.X86.HPrime.F0 s₀ t := by
  refine ⟨h.body.keeps hp k, h.out.keeps hp k, k.ebp.trans h.ebp, ?_⟩
  have hif := hp.in_fits
  have := k.bytes (R := VG.Proof.Argon2.X86.HPrime.inR s₀) (by simp; omega)
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in.symm
  simp only at this
  rw [this, h.input]

theorem nF_pos : 1 ≤ VG.Proof.Argon2.X86.HPrime.nF s₀ := by have := hp.ol_pos; simp only [VG.Proof.Argon2.X86.HPrime.nF]; omega

theorem first_choose {s : State} (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s) :
    WP isa chooseLength s fun t => VG.Proof.Argon2.X86.HPrime.F0 s₀ t ∧ t.gpr .edx = BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.nF s₀) :=
  (VG.Proof.Argon2.X86.HPrime.choose_ok hp h.body h.out).mono fun _ ⟨e, k⟩ => ⟨h.keeps hp k, e⟩

theorem first_init {s : State} (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s ∧ s.gpr .edx = BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.nF s₀)) :
    WP isa VG.Impl.Argon2.X86.HPrime.init s fun t => VG.Proof.Argon2.X86.HPrime.F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (VG.Proof.Argon2.X86.HPrime.nF s₀) 0) t.mem (VG.Proof.Argon2.X86.HPrime.P s₀) [] := by
  have c := h.1.body.ctx hp
  refine (VG.Proof.Argon2.X86.HPrime.init_ok c h.2 (VG.Proof.Argon2.X86.HPrime.nF_pos hp) (Nat.min_le_right _ _)).mono fun t ⟨r, cs, rd, wr, f⟩ => ⟨?_, r⟩
  refine h.1.keeps hp (Keeps.of_call (VG.Proof.Argon2.X86.HPrime.of_callee cs) rd wr f fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩

theorem pfx_cov {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) : Covers [⟨VG.Proof.Argon2.X86.HPrime.P s₀ + BitVec.ofNat 64 832, 4⟩] s.wr := by
  rw [b.wr, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp, 832, rfl, by simp⟩

theorem first_fixed {s : State}
    (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s ∧ Repr b (Spec.Blake2.init b (VG.Proof.Argon2.X86.HPrime.nF s₀) 0) s.mem (VG.Proof.Argon2.X86.HPrime.P s₀) []) :
    WP isa (absorbFixed 832 4) s fun t => VG.Proof.Argon2.X86.HPrime.F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (VG.Proof.Argon2.X86.HPrime.nF s₀) 0) t.mem (VG.Proof.Argon2.X86.HPrime.P s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀)) := by
  have hs := hp.scr_fits
  refine (VG.Proof.Argon2.X86.HPrime.absorbFixed_ok (h.1.body.ctx hp) (offset := 832) (size := 4) (by omega) (by decide)
    (by decide) (VG.Proof.Argon2.X86.HPrime.pfx_cov hp h.1.body) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))) h.2).mono
    fun t ⟨r, k⟩ => ⟨h.1.keeps hp k, ?_⟩
  rw [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, h.1.body.pfx] at r
  exact r

/-- The instructions before `absorbInput`'s call of `update`. -/
theorem absorbInput_blk {s : State} (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s) :
    WP isa (.block [.mov .ecx (.imm 4), .mov .edx (.imm 0), .mov .esi (.mem (at_ .esp 4)),
      .mov .edi (.mem (at_ .esp 8))]) s fun t =>
      VG.Proof.Argon2.X86.HPrime.UpdateIn (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (VG.Proof.Argon2.X86.HPrime.inp s₀) (VG.Proof.Argon2.X86.HPrime.inl s₀) 4 0 t ∧ VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t ∧ t.mem = s.mem := by
  have b := h.body
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ =>
    wp_movm (VG.Proof.Sha512.X86.ea_of (by rw [u₅.other _ (by decide), u₄.other _ (by decide), b.esp])
      4) (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact b.arg_in hp (i := 0) (by decide)) fun s₆ u₆ =>
    wp_movm (VG.Proof.Sha512.X86.ea_of (by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b.esp]) 8)
      (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact b.arg_in hp (i := 1) (by decide)) fun s₇ u₇ =>
    WP.block_nil ?_
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have o₇ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₇.other _ h4, u₆.other _ h3, u₅.other _ h2, u₄.other _ h1]
  have k₇ : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s s₇ := Keeps.same (o₇ _ (by decide) (by decide) (by decide) (by decide))
    (o₇ _ (by decide) (by decide) (by decide) (by decide)) (o₇ _ (by decide) (by decide) (by decide) (by decide))
    m₇ (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr])
  have b₇ := b.keeps hp k₇
  refine ⟨⟨b₇.ctx hp, ?_, ?_, ?_, ?_, ?_⟩, k₇, m₇⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]; exact b.arg hp (i := 0) (by decide)
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, b.arg hp (i := 1) (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [b₇.rd, b₇.wr, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.X86.HPrime.inR s₀, by simp, 0, by simp, by simp⟩

theorem first_input {s : State}
    (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s ∧ Repr b (Spec.Blake2.init b (VG.Proof.Argon2.X86.HPrime.nF s₀) 0) s.mem (VG.Proof.Argon2.X86.HPrime.P s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀))) :
    WP isa absorbInput s fun t => VG.Proof.Argon2.X86.HPrime.F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (VG.Proof.Argon2.X86.HPrime.nF s₀) 0) t.mem (VG.Proof.Argon2.X86.HPrime.P s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀) ++ VG.Proof.Argon2.X86.HPrime.inB s₀) := by
  have hif := hp.in_fits
  have hil := (VG.X86.arg s₀ 1).isLt
  unfold absorbInput
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.absorbInput_blk hp h.1).mono fun s₇ ⟨⟨c₇, esi₇, edi₇, x₇, y₇, hDc⟩, k₇, m₇⟩ => ?_)
  have cnt₇ : s₇.gpr .edx ++ s₇.gpr .ecx = BitVec.ofNat 64 (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀)).length := by
    rw [Proof.Argon2.le32_length, x₇, y₇]; rfl
  have F₇ := h.1.keeps hp k₇
  refine (VG.Proof.Argon2.X86.HPrime.update_ok c₇ (h0 := Spec.Blake2.init Spec.Blake2.b (VG.Proof.Argon2.X86.HPrime.nF s₀) 0) esi₇ edi₇ hif hDc
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in (by rw [m₇]; exact h.2) cnt₇
    (by rw [Proof.Argon2.le32_length]; omega)).mono fun s₈ ⟨r₈, cs₈, rd₈, wr₈, f₈⟩ => ?_
  rw [F₇.input] at r₈
  refine ⟨F₇.keeps hp (Keeps.of_call (VG.Proof.Argon2.X86.HPrime.of_callee cs₈) rd₈ wr₈ f₈ fun r hr => ?_), r₈⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- The count of the prefix and the input, as `finishInput` passes it. -/
abbrev cntLo (s₀ : State) : BitVec 32 := BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.inl s₀ + 4)
abbrev cntHi (s₀ : State) : BitVec 32 := BitVec.ofNat 32 ((VG.Proof.Argon2.X86.HPrime.inl s₀ + 4) / 2 ^ 32)

/-- The instructions before `finishInput`'s call of `finalize`. -/
theorem finishInput_blk {s : State} (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s) :
    WP isa (.block [.mov .ecx (.mem (at_ .esp 8)), .mov .edx (.imm 0), .alu .add .ecx (.imm 4),
      .alu .adc .edx (.imm 0)]) s fun t =>
      VG.Proof.Argon2.X86.HPrime.FinalizeIn (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (VG.Proof.Argon2.X86.HPrime.cntLo s₀) (VG.Proof.Argon2.X86.HPrime.cntHi s₀) t ∧ VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t ∧
        t.mem = s.mem := by
  have hil := (VG.X86.arg s₀ 1).isLt
  have b := h.body
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.esp 8) (b.arg_in hp (i := 1) (by decide))
    fun s₉ u₉ => wp_movi fun s₁₀ u₁₀ => wp_addC fun s₁₁ u₁₁ cf₁₁ => wp_adcC cf₁₁ fun s₁₂ u₁₂ _ =>
    WP.block_nil ?_
  have m₁₂ : s₁₂.mem = s.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have o₁₂ : ∀ r, r ≠ .ecx → r ≠ .edx → s₁₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₁₂.other _ h2, u₁₁.other _ h1, u₁₀.other _ h2, u₉.other _ h1]
  have k₁₂ : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s s₁₂ := Keeps.same (o₁₂ _ (by decide) (by decide))
    (o₁₂ _ (by decide) (by decide)) (o₁₂ _ (by decide) (by decide)) m₁₂
    (by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd]) (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr])
  have ecx₉ : s₉.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.inl s₀) := by
    rw [u₉.gpr, b.arg hp (i := 1) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨(b.keeps hp k₁₂).ctx hp, ?_, ?_⟩, k₁₂, m₁₂⟩
  · show _ = BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.inl s₀ + 4)
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), ecx₉, BitVec.ofNat_add]; rfl
  · show _ = BitVec.ofNat 32 ((VG.Proof.Argon2.X86.HPrime.inl s₀ + 4) / 2 ^ 32)
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₁₀.other _ (by decide), ecx₉]
    rw [← Proof.Blake2.X86.Stream.carry_ofNat (VG.Proof.Argon2.X86.HPrime.inl s₀) 4 (by decide), Nat.div_eq_of_lt hil]
    rfl

theorem first_finish {s : State}
    (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s ∧ Repr b (Spec.Blake2.init b (VG.Proof.Argon2.X86.HPrime.nF s₀) 0) s.mem (VG.Proof.Argon2.X86.HPrime.P s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀) ++ VG.Proof.Argon2.X86.HPrime.inB s₀)) :
    WP isa finishInput s fun t => VG.Proof.Argon2.X86.HPrime.F0 s₀ t ∧
      (VG.Proof.Argon2.X86.HPrime.digest s₀ t).take (VG.Proof.Argon2.X86.HPrime.nF s₀) = Spec.Argon2.H (VG.Proof.Argon2.X86.HPrime.nF s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀) ++ VG.Proof.Argon2.X86.HPrime.inB s₀) := by
  have hif := hp.in_fits
  unfold finishInput
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.finishInput_blk hp h.1).mono fun s₁₂ ⟨⟨c₁₂, x₁₂, y₁₂⟩, k₁₂, m₁₂⟩ => ?_)
  have cnt : s₁₂.gpr .edx ++ s₁₂.gpr .ecx =
      BitVec.ofNat 64 (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀) ++ VG.Proof.Argon2.X86.HPrime.inB s₀).length := by
    rw [x₁₂, y₁₂, List.length_append, Proof.Argon2.le32_length]
    simp only [VG.Proof.Argon2.X86.HPrime.inB, bytesAt, List.length_map, List.length_range]
    apply BitVec.eq_of_toNat_eq
    rw [Proof.Blake2.X86.Stream.append_ofNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have F₁₂ := h.1.keeps hp k₁₂
  refine (VG.Proof.Argon2.X86.HPrime.finalize_ok c₁₂ (by rw [m₁₂]; exact h.2) cnt
    (by simp only [List.length_append, Proof.Argon2.le32_length, VG.Proof.Argon2.X86.HPrime.inB, bytesAt, List.length_map,
      List.length_range]; omega)).mono ?_
  rintro t ⟨d, cs, rd, wr, f⟩
  refine ⟨F₁₂.keeps hp (Keeps.of_call (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact cs _ (by decide) (by decide)) rd wr f fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show (bytesAt t.mem ((VG.Proof.Argon2.X86.HPrime.scr s₀).setWidth 64 + 768) 64).take _ = _
    rw [d, Proof.Argon2.H_stream]

/-- `first` hashes the length prefix and the input. -/
theorem first_ok {s : State} (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s) :
    WP isa first s fun t => VG.Proof.Argon2.X86.HPrime.F0 s₀ t ∧
      (VG.Proof.Argon2.X86.HPrime.digest s₀ t).take (VG.Proof.Argon2.X86.HPrime.nF s₀) = Spec.Argon2.H (VG.Proof.Argon2.X86.HPrime.nF s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀) ++ VG.Proof.Argon2.X86.HPrime.inB s₀) := by
  unfold first
  exact WP.seq ((VG.Proof.Argon2.X86.HPrime.first_choose hp h).mono fun _ h₁ => WP.seq ((VG.Proof.Argon2.X86.HPrime.first_init hp h₁).mono fun _ h₂ =>
    WP.seq ((VG.Proof.Argon2.X86.HPrime.first_fixed hp h₂).mono fun _ h₃ => WP.seq ((VG.Proof.Argon2.X86.HPrime.first_input hp h₃).mono fun _ h₄ =>
      VG.Proof.Argon2.X86.HPrime.first_finish hp h₄))))

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the chain of 64-byte hashes

`chain_ok`: after the first prefix V₁[0, 32) of a long output, each iteration
hashes the digest again and emits the prefix of the new one, while more than
64 bytes are left. The output is then V₁[0, 32) ‖ `chainPrefixes j V₁` and the
digest `chainDigest j V₁`, with 33 to 64 bytes left.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_movi wp_movm wp_cmpi)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem chainDigest_succ' (j : Nat) (v : List Byte) :
    chainDigest (j + 1) v = Spec.Argon2.H 64 (chainDigest j v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih => exact ih (Spec.Argon2.H 64 v)

theorem chainPrefixes_succ' (j : Nat) (v : List Byte) :
    chainPrefixes (j + 1) v = chainPrefixes j v ++ (Spec.Argon2.H 64 (chainDigest j v)).take 32 := by
  induction j generalizing v with
  | zero => simp [chainPrefixes, chainDigest]
  | succ j ih =>
    rw [chainPrefixes, ih, chainPrefixes, chainDigest, List.append_assoc]

theorem finalHash_length (h0 : HashValue 64) (d : List Byte) : (finalHash b h0 d).length = 64 := by
  simp only [finalHash, Proof.Argon2.wordList_length, Vector.length_toList]

/-- The output after `j` iterations. -/
abbrev chainOut (V : List Byte) (j : Nat) : List Byte := V.take 32 ++ chainPrefixes j V

theorem chainOut_length {V : List Byte} (hV : V.length = 64) (j : Nat) :
    (VG.Proof.Argon2.X86.HPrime.chainOut V j).length = 32 + 32 * j := by
  simp only [VG.Proof.Argon2.X86.HPrime.chainOut, List.length_append, List.length_take, hV, Proof.Argon2.chainPrefixes_length]
  omega

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀)
include hp

/-- `cmpLeft`: CF is whether fewer than 65 bytes are left. -/
theorem cmp_ok {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) {xs : List Byte} (o : VG.Proof.Argon2.X86.HPrime.Out s₀ s xs) :
    WP isa (.block cmpLeft) s fun t => t.cf = some (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length < 65)) ∧
      VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t ∧ t.mem = s.mem := by
  have hs := hp.scr_fits
  have hol : VG.Proof.Argon2.X86.HPrime.ol s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  unfold cmpLeft
  have rl : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]
    exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ⟨?_, ?_, by rw [f₂.mem, u₁.mem]⟩
  · rw [cf₂, u₁.gpr, o.left, Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega)]; rfl
  · exact Keeps.same (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
      (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd])
      (by rw [f₂.wr, u₁.wr])

/-- What the chain keeps between iterations. -/
structure ChainInv (s₀ : State) (e : BitVec 32) (V : List Byte) (j : Nat) (s : State) : Prop where
  body : VG.Proof.Argon2.X86.HPrime.Body s₀ s
  ebp : s.gpr .ebp = e
  out : VG.Proof.Argon2.X86.HPrime.Out s₀ s (VG.Proof.Argon2.X86.HPrime.chainOut V j)
  digest : VG.Proof.Argon2.X86.HPrime.digest s₀ s = chainDigest j V

/-- One iteration. -/
theorem iter_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : VG.Proof.Argon2.X86.HPrime.ChainInv s₀ e V j s) (hl : 32 + 32 * j + 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) :
    WP isa (.seq (.block [.mov .edx (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) s
      fun t => VG.Proof.Argon2.X86.HPrime.ChainInv s₀ e V (j + 1) t ∧
        t.cf = some (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * (j + 1)) < 65)) := by
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s s₁ := Keeps.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  have b₁ := h.body.keeps hp k₁
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.next_ok (b₁.ctx hp) (n := 64) u₁.gpr (by decide) (by decide)).mono
    fun s₂ ⟨d₂, k₂⟩ => ?_)
  have K₂ := k₁.trans k₂
  have b₂ := h.body.keeps hp K₂
  have o₂ := h.out.keeps hp K₂
  have hlen := VG.Proof.Argon2.X86.HPrime.chainOut_length hV j
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.emit_ok hp b₂ o₂ (by rw [hlen]; exact hl)).mono fun s₃ ⟨b₃, e₃, o₃, d₃⟩ => ?_)
  have dg : VG.Proof.Argon2.X86.HPrime.digest s₀ s₂ = chainDigest (j + 1) V := by
    rw [VG.Proof.Argon2.X86.HPrime.chainDigest_succ', ← h.digest, Proof.Argon2.H_stream,
      List.take_of_length_le (by rw [VG.Proof.Argon2.X86.HPrime.finalHash_length])]
    rw [u₁.mem] at d₂
    exact d₂
  have xs₃ : VG.Proof.Argon2.X86.HPrime.chainOut V j ++ (VG.Proof.Argon2.X86.HPrime.digest s₀ s₂).take 32 = VG.Proof.Argon2.X86.HPrime.chainOut V (j + 1) := by
    rw [dg, VG.Proof.Argon2.X86.HPrime.chainDigest_succ', VG.Proof.Argon2.X86.HPrime.chainOut, VG.Proof.Argon2.X86.HPrime.chainOut, VG.Proof.Argon2.X86.HPrime.chainPrefixes_succ', List.append_assoc]
  rw [xs₃] at o₃
  refine (VG.Proof.Argon2.X86.HPrime.cmp_ok hp b₃ o₃).mono fun t ⟨cf, k, m⟩ => ⟨⟨b₃.keeps hp k, ?_, o₃.keeps hp k, ?_⟩, ?_⟩
  · rw [k.ebp, e₃, K₂.ebp, h.ebp]
  · show bytesAt _ _ _ = _
    rw [m]
    exact d₃.trans dg
  · rw [cf, VG.Proof.Argon2.X86.HPrime.chainOut_length hV]

/-- The chain: iterations while more than 64 bytes are left. -/
theorem chain_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : VG.Proof.Argon2.X86.HPrime.ChainInv s₀ e V j s) (hl : 65 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j)) :
    WP isa chain s fun t => ∃ j', VG.Proof.Argon2.X86.HPrime.ChainInv s₀ e V j' t ∧ 33 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j') ∧
      VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j') ≤ 64 ∧ 32 + 32 * j' ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ := by
  unfold chain
  refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ j', m = VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j') ∧ VG.Proof.Argon2.X86.HPrime.ChainInv s₀ e V j' t ∧ 65 ≤ m)
    ?_ (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j)) s ⟨j, rfl, h, hl⟩
  rintro m t ⟨j', rfl, hi, hm⟩
  refine (VG.Proof.Argon2.X86.HPrime.iter_ok hp hV hi (by omega)).mono fun u ⟨hu, cf⟩ => ?_
  by_cases hc : VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * (j' + 1)) < 65
  · refine .inl ⟨?_, j' + 1, hu, by omega, by omega, by omega⟩
    show u.cf.map (!·) = some false
    rw [cf]; simp [hc]
  · refine .inr ⟨?_, _, by omega, j' + 1, rfl, hu, by omega⟩
    show u.cf.map (!·) = some true
    rw [cf]; simp [hc]

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the output from the first digest

`finish_ok`: `finishOutput` writes H′ to the output, from the first digest:
the digest itself for at most 64 bytes, and otherwise its prefix, the chain
and the last hash (`extend_ok`), of the 33 to 64 bytes left.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀)
include hp

/-- What the chain leaves: the output after `j` iterations and the last hash. -/
def Extended (s₀ : State) (e : BitVec 32) (V : List Byte) (t : State) : Prop :=
  ∃ j, VG.Proof.Argon2.X86.HPrime.Body s₀ t ∧ t.gpr .ebp = e ∧ VG.Proof.Argon2.X86.HPrime.Out s₀ t (VG.Proof.Argon2.X86.HPrime.chainOut V j) ∧
    (VG.Proof.Argon2.X86.HPrime.digest s₀ t).take (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j)) =
      Spec.Argon2.H (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j)) (chainDigest j V) ∧
    33 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) ∧ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ VG.Proof.Argon2.X86.HPrime.ol s₀

theorem extend_ok {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) (o : VG.Proof.Argon2.X86.HPrime.Out s₀ s []) (hol : 65 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) :
    WP isa extendDigest s (VG.Proof.Argon2.X86.HPrime.Extended s₀ (s.gpr .ebp) (VG.Proof.Argon2.X86.HPrime.digest s₀ s)) := by
  have hs := hp.scr_fits
  have hV : (VG.Proof.Argon2.X86.HPrime.digest s₀ s).length = 64 := by simp [VG.Proof.Argon2.X86.HPrime.digest, bytesAt]
  unfold extendDigest
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.emit_ok hp b o (by simp only [List.length_nil]; omega)).mono
    fun s₁ ⟨b₁, e₁, o₁, d₁⟩ => ?_)
  rw [List.nil_append, show (VG.Proof.Argon2.X86.HPrime.digest s₀ s).take 32 = VG.Proof.Argon2.X86.HPrime.chainOut (VG.Proof.Argon2.X86.HPrime.digest s₀ s) 0 by
    simp [VG.Proof.Argon2.X86.HPrime.chainOut, chainPrefixes]] at o₁
  have i₁ : VG.Proof.Argon2.X86.HPrime.ChainInv s₀ (s.gpr .ebp) (VG.Proof.Argon2.X86.HPrime.digest s₀ s) 0 s₁ := ⟨b₁, e₁, o₁, d₁⟩
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.cmp_ok hp b₁ o₁).mono fun s₂ ⟨cf₂, k₂, m₂⟩ => ?_)
  rw [VG.Proof.Argon2.X86.HPrime.chainOut_length hV] at cf₂
  have i₂ : VG.Proof.Argon2.X86.HPrime.ChainInv s₀ (s.gpr .ebp) (VG.Proof.Argon2.X86.HPrime.digest s₀ s) 0 s₂ :=
    ⟨b₁.keeps hp k₂, k₂.ebp.trans e₁, o₁.keeps hp k₂, by show bytesAt _ _ _ = _; rw [m₂]; exact d₁⟩
  have hIte : WP isa (.ite .b (.block []) chain) s₂ fun t => ∃ j, VG.Proof.Argon2.X86.HPrime.ChainInv s₀ (s.gpr .ebp) (VG.Proof.Argon2.X86.HPrime.digest s₀ s) j t ∧
      33 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) ∧ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ := by
    refine WP.ite (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * 0) < 65)) cf₂ (fun h => WP.block_nil ⟨0, i₂, ?_⟩)
      (fun h => (VG.Proof.Argon2.X86.HPrime.chain_ok hp hV i₂ ?_).mono fun t h => h)
    · simp only [decide_eq_true_eq] at h; omega
    · simp only [decide_eq_false_iff_not] at h; omega
  refine WP.seq (hIte.mono fun s₃ ⟨j, i₃, l₁, l₂, l₃⟩ => ?_)
  have rl : InRegions (s₃.rd ++ s₃.wr) (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) 4 := by
    rw [i₃.body.rd, i₃.body.wr]
    exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of i₃.body.ebx leftOff) rl fun s₄ u₄ => WP.block_nil ?_)
  have k₄ : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s₃ s₄ := Keeps.same (u₄.other _ (by decide)) (u₄.other _ (by decide))
    (u₄.other _ (by decide)) u₄.mem u₄.rd u₄.wr
  have b₄ := i₃.body.keeps hp k₄
  have edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j)) := by
    rw [u₄.gpr, i₃.out.left, VG.Proof.Argon2.X86.HPrime.chainOut_length hV]
  refine (VG.Proof.Argon2.X86.HPrime.next_ok (b₄.ctx hp) edx₄ (by omega) l₂).mono fun t ⟨d, k⟩ => ?_
  have K := k₄.trans k
  refine ⟨j, i₃.body.keeps hp K, by rw [K.ebp, i₃.ebp], i₃.out.keeps hp K, ?_, l₁, l₂, l₃⟩
  rw [Proof.Argon2.H_stream, ← i₃.digest]
  rw [u₄.mem] at d
  exact congrArg (List.take _) d

/-- `finishOutput` writes H′ of the input `I` from its first digest. -/
theorem finish_ok {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) (o : VG.Proof.Argon2.X86.HPrime.Out s₀ s []) {I : List Byte}
    (hd : (VG.Proof.Argon2.X86.HPrime.digest s₀ s).take (min (VG.Proof.Argon2.X86.HPrime.ol s₀) 64) =
      Spec.Argon2.H (min (VG.Proof.Argon2.X86.HPrime.ol s₀) 64) (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀) ++ I)) :
    WP isa finishOutput s fun t => VG.Proof.Argon2.X86.HPrime.Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.HPrime.op s₀).setWidth 64) (VG.Proof.Argon2.X86.HPrime.ol s₀) = Spec.Argon2.hPrime (VG.Proof.Argon2.X86.HPrime.ol s₀) I := by
  have hpos := hp.ol_pos
  have hV : (VG.Proof.Argon2.X86.HPrime.digest s₀ s).length = 64 := by simp [VG.Proof.Argon2.X86.HPrime.digest, bytesAt]
  unfold finishOutput
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.cmp_ok hp b o).mono fun s₁ ⟨cf₁, k₁, m₁⟩ => ?_)
  simp only [List.length_nil, Nat.sub_zero] at cf₁
  have b₁ := b.keeps hp k₁
  have o₁ := o.keeps hp k₁
  have d₁ : VG.Proof.Argon2.X86.HPrime.digest s₀ s₁ = VG.Proof.Argon2.X86.HPrime.digest s₀ s := by show bytesAt _ _ _ = _; rw [m₁]
  have hIte : WP isa (.ite .b (.block []) extendDigest) s₁ fun t => VG.Proof.Argon2.X86.HPrime.Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      ∃ xs, VG.Proof.Argon2.X86.HPrime.Out s₀ t xs ∧ xs.length < VG.Proof.Argon2.X86.HPrime.ol s₀ ∧ VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length ≤ 64 ∧
        xs ++ (VG.Proof.Argon2.X86.HPrime.digest s₀ t).take (VG.Proof.Argon2.X86.HPrime.ol s₀ - xs.length) = Spec.Argon2.hPrime (VG.Proof.Argon2.X86.HPrime.ol s₀) I := by
    refine WP.ite (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ < 65)) cf₁ (fun h => WP.block_nil ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      refine ⟨b₁, k₁.ebp, [], o₁, by simp only [List.length_nil]; omega,
        by simp only [List.length_nil]; omega, ?_⟩
      rw [Nat.min_eq_left (by omega)] at hd
      rw [List.nil_append, List.length_nil, Nat.sub_zero, d₁, hd]
      simp only [Spec.Argon2.hPrime, eq_true (by omega : ol s₀ ≤ 64), ite_true]
    · simp only [decide_eq_false_iff_not] at h
      refine (VG.Proof.Argon2.X86.HPrime.extend_ok hp b₁ o₁ (by omega)).mono fun t ⟨j, bt, et, ot, dt, l₁, l₂, l₃⟩ =>
        ⟨bt, et.trans k₁.ebp, _, ot, ?_, ?_, ?_⟩
      · rw [VG.Proof.Argon2.X86.HPrime.chainOut_length (by rw [d₁]; exact hV)]; omega
      · rw [VG.Proof.Argon2.X86.HPrime.chainOut_length (by rw [d₁]; exact hV)]; omega
      · have V₁ : VG.Proof.Argon2.X86.HPrime.digest s₀ s₁ = Spec.Argon2.H 64 (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀) ++ I) := by
          rw [d₁, ← List.take_of_length_le (l := VG.Proof.Argon2.X86.HPrime.digest s₀ s) (i := 64) (by rw [hV]),
            ← Nat.min_eq_right (by omega : 64 ≤ ol s₀), hd]
        rw [VG.Proof.Argon2.X86.HPrime.chainOut_length (by rw [d₁]; exact hV), dt, VG.Proof.Argon2.X86.HPrime.chainOut, ← Proof.Argon2.longHash_chain, V₁]
        have hr : (VG.Proof.Argon2.X86.HPrime.ol s₀ + 31) / 32 - 2 = j + 1 := by omega
        simp only [Spec.Argon2.hPrime, eq_false (by omega : ¬ ol s₀ ≤ 64), ite_false]
        rw [hr, show VG.Proof.Argon2.X86.HPrime.ol s₀ - 32 * (j + 1) = VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) by omega]
  refine WP.seq (hIte.mono fun s₂ ⟨b₂, e₂, xs, o₂, l₁, l₂, h₂⟩ => ?_)
  refine (VG.Proof.Argon2.X86.HPrime.copyRemaining_ok hp b₂ o₂ l₁ l₂).mono fun t ⟨bt, et, ht⟩ => ⟨bt, et.trans e₂, ?_⟩
  rw [ht, h₂]

end

end VG.Proof.Argon2.X86.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.HPrime.HashCT`. -/
section

/-!
# Argon2 H′ on x86 (32-bit): the hash macros, in two runs

`absorbFixed_rel` and `next_rel`: hashing a fixed buffer of `scratch`, and
the digest, leak the same trace in two runs with the same `scratch` and
stack pointer.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed next)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-- The instructions before `absorbFixed`'s call of `update`. -/
theorem absorbFixed_blk {B E : BitVec 32} {s : State} (c : VG.Proof.Argon2.X86.HPrime.Ctx B E s) {offset size : Nat}
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hs : 0 < size) (hlt : size < 2 ^ 32)
    (hcov : Covers [⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩] s.wr) :
    WP isa (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0), .mov .esi (.reg .ebx),
      .alu .add .esi (.imm (BitVec.ofNat 32 offset)), .mov .edi (.imm (BitVec.ofNat 32 size))]) s
      (VG.Proof.Argon2.X86.HPrime.UpdateIn B E (B + BitVec.ofNat 32 offset) size 0 0) := by
  have hfit := c.fits
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    wp_movi fun s₅ u₅ => WP.block_nil ?_
  have o : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have w : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨c.of_regs (o _ (by decide) (by decide) (by decide) (by decide))
    (o _ (by decide) (by decide) (by decide) (by decide)) w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.ebx]
  · rw [u₅.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [VG.Proof.Argon2.X86.HPrime.setWidth_add (by omega), show s₅.rd ++ s₅.wr = s.rd ++ s.wr by
      rw [w, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]]
    exact Covers.right hcov

/-- What `absorbFixed` needs: the context, and the buffer writable. -/
def FixedIn (B E : BitVec 32) (offset size : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.X86.HPrime.Ctx B E s ∧ Covers [⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩] s.wr

theorem absorbFixed_rel {B E : BitVec 32} {offset size : Nat} (ho : B.toNat + offset + size ≤ 2 ^ 32)
    (hlo : 768 ≤ offset) (hs : 0 < size)
    (hstk : (below E 60).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩)
    (hc : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebx]) (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm (BitVec.ofNat 32 offset)),
      .mov .edi (.imm (BitVec.ofNat 32 size))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.HPrime.FixedIn B E offset size s₁ ∧ VG.Proof.Argon2.X86.HPrime.FixedIn B E offset size s₂)
      (absorbFixed offset size) fun _ _ => True := by
  have eD : (B + BitVec.ofNat 32 offset).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 offset :=
    VG.Proof.Argon2.X86.HPrime.setWidth_add (by omega)
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]; omega
  unfold absorbFixed
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx] (fun s₁ s₂ ⟨c₁, _⟩ ⟨c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]) hc
    (fun s ⟨c, h⟩ => VG.Proof.Argon2.X86.HPrime.absorbFixed_blk c ho hs (by omega) h) (fun s ⟨c, h⟩ => VG.Proof.Argon2.X86.HPrime.absorbFixed_blk c ho hs (by omega) h))
    (VG.Proof.Argon2.X86.HPrime.update_rel (by rw [dTo]; omega) (by rw [eD]; exact Offset.disjoint_base _ hlo (by omega))
      (by rw [eD]; exact hstk))

/-- The instructions before `absorbFixed`'s call, from `esp` and `ebx` public. -/
abbrev FixedCheck (offset size : Nat) : Prop :=
  ∃ hc, (VG.Taint.check taint (τr [.esp, .ebx]) (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm (BitVec.ofNat 32 offset)),
      .mov .edi (.imm (BitVec.ofNat 32 size))]) hc).isSome = true

theorem fixed_check_768 : VG.Proof.Argon2.X86.HPrime.FixedCheck 768 64 := ⟨_, by taint_decide⟩
theorem fixed_check_832 : VG.Proof.Argon2.X86.HPrime.FixedCheck 832 4 := ⟨_, by taint_decide⟩

/-- `next`, from the context and the digest length in `edx`. -/
theorem next_rel {B E : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86.HPrime.InitIn B E n s₁ ∧ VG.Proof.Argon2.X86.HPrime.InitIn B E n s₂) next fun _ _ => True := by
  have st : ∀ s, VG.Proof.Argon2.X86.HPrime.InitIn B E n s → WP isa VG.Impl.Argon2.X86.HPrime.init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (B.setWidth 64) [] ∧ VG.Proof.Argon2.X86.HPrime.Ctx B E t := fun s ⟨c, e⟩ =>
    (VG.Proof.Argon2.X86.HPrime.init_ok c e hn₁ hn₂).mono fun t ⟨r, cs, _, wr, _⟩ =>
      ⟨r, c.of_regs (cs _ (by decide)) (cs _ (by decide)) wr⟩
  have fx : ∀ s, Repr b (Spec.Blake2.init b n 0) s.mem (B.setWidth 64) [] ∧ VG.Proof.Argon2.X86.HPrime.Ctx B E s →
      WP isa (absorbFixed 768 64) s fun t => VG.Proof.Argon2.X86.HPrime.Ctx B E t := fun s ⟨r, c⟩ =>
    (VG.Proof.Argon2.X86.HPrime.absorbFixed_ok c (offset := 768) (size := 64) (by have := c.fits; omega) (by decide) (by decide)
      (c.cov (by decide)) (c.stk_sub (by decide) (by decide)) r).mono fun t ⟨_, k⟩ => k.ctx c
  have fin : ∀ s, VG.Proof.Argon2.X86.HPrime.Ctx B E s → WP isa (.block [.mov .ecx (.imm 64), .mov .edx (.imm 0)]) s
      (VG.Proof.Argon2.X86.HPrime.FinalizeIn B E 64 0) := fun s c =>
    wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil
      ⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩
  unfold next
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_wp (VG.Proof.Argon2.X86.HPrime.init_rel hn₁ hn₂) st st)
    (RelCT.seq (R := fun s₁ s₂ => VG.Proof.Argon2.X86.HPrime.Ctx B E s₁ ∧ VG.Proof.Argon2.X86.HPrime.Ctx B E s₂) ?_
      (RelCT.seq (R := fun s₁ s₂ => VG.Proof.Argon2.X86.HPrime.FinalizeIn B E 64 0 s₁ ∧ VG.Proof.Argon2.X86.HPrime.FinalizeIn B E 64 0 s₂) ?_ VG.Proof.Argon2.X86.HPrime.finalize_rel))
  · refine VG.Proof.Argon2.X86.HPrime.rel_wp (RelCT.of_pre fun s₁ _ ⟨⟨_, c₁⟩, _⟩ =>
      (VG.Proof.Argon2.X86.HPrime.absorbFixed_rel (B := B) (E := E) (offset := 768) (size := 64) (by have := c₁.fits; omega)
        (by decide) (by decide) (c₁.stk_sub (by decide) (by decide)) VG.Proof.Argon2.X86.HPrime.fixed_check_768).mono
      (fun s₁ s₂ ⟨⟨_, c₁⟩, ⟨_, c₂⟩⟩ => ⟨⟨c₁, c₁.cov (by decide)⟩, ⟨c₂, c₂.cov (by decide)⟩⟩)
      fun _ _ h => h) fx fx
  · exact VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx] (fun s₁ s₂ c₁ c₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]) ⟨_, by taint_decide⟩ fin fin

end VG.Proof.Argon2.X86.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.HPrime.FinishCT`. -/
section

section

/-!
# Argon2 H′ on x86 (32-bit): the output, in two runs

Two runs of H′ with the same public data (`Same`: the stack pointer and the
arguments) write their output through the same addresses: `copy_rel`,
`emit_rel` and `copyRemaining_rel`, from states with the same number of
output bytes written.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy emitPrefix copyRemaining outOff leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_mov wp_addi wp_movm contains_addr)

/-- The public data of two runs. -/
structure Same (s₀ s₀' : State) : Prop where
  esp : VG.Proof.Argon2.X86.HPrime.esp₀ s₀' = VG.Proof.Argon2.X86.HPrime.esp₀ s₀
  args : ∀ i < 5, VG.X86.arg s₀' i = VG.X86.arg s₀ i

theorem Same.of_pub {s₀ s₀' : State} (h : hPrimeX86.pub s₀ s₀') : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀' :=
  ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩

section
variable {s₀ s₀' : State} (q : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀')
include q

theorem Same.scr_eq : VG.Proof.Argon2.X86.HPrime.scr s₀' = VG.Proof.Argon2.X86.HPrime.scr s₀ := q.args 4 (by decide)
theorem Same.op_eq : VG.Proof.Argon2.X86.HPrime.op s₀' = VG.Proof.Argon2.X86.HPrime.op s₀ := q.args 2 (by decide)
theorem Same.ol_eq : VG.Proof.Argon2.X86.HPrime.ol s₀' = VG.Proof.Argon2.X86.HPrime.ol s₀ := by
  show (VG.X86.arg s₀' 3).toNat = (VG.X86.arg s₀ 3).toNat; rw [q.args 3 (by decide)]
theorem Same.inp_eq : VG.Proof.Argon2.X86.HPrime.inp s₀' = VG.Proof.Argon2.X86.HPrime.inp s₀ := q.args 0 (by decide)
theorem Same.inl_eq : VG.Proof.Argon2.X86.HPrime.inl s₀' = VG.Proof.Argon2.X86.HPrime.inl s₀ := by
  show (VG.X86.arg s₀' 1).toNat = (VG.X86.arg s₀ 1).toNat; rw [q.args 1 (by decide)]

end

/-! ## `copy` -/

/-- What `copy` needs: the body, `k` bytes of output written, and `n` to copy. -/
def CopyIn (s₀ : State) (k n : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.X86.HPrime.Body s₀ s ∧ VG.Proof.Argon2.X86.HPrime.OutPtr s₀ s k ∧ s.gpr .esi = BitVec.ofNat 32 n

/-- The registers after `copy`'s first instructions. -/
def CopyRegs (s₀ : State) (k n : Nat) (t : State) : Prop :=
  t.gpr .esp = VG.Proof.Argon2.X86.HPrime.esp₀ s₀ ∧ t.gpr .ebx = VG.Proof.Argon2.X86.HPrime.scr s₀ ∧ t.gpr .edx = VG.Proof.Argon2.X86.HPrime.scr s₀ + 768 ∧
    t.gpr .edi = VG.Proof.Argon2.X86.HPrime.op s₀ + BitVec.ofNat 32 k ∧ t.gpr .esi = BitVec.ofNat 32 n

theorem copy_blk {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) {k n : Nat} {s : State} (h : VG.Proof.Argon2.X86.HPrime.CopyIn s₀ k n s) :
    WP isa (.block [.mov .edx (.reg .ebx), .alu .add .edx (.imm 768), .mov .edi (.mem (VG.Impl.Sha512.X86.at_ .ebx outOff))])
      s (VG.Proof.Argon2.X86.HPrime.CopyRegs s₀ k n) := by
  obtain ⟨b, hk, hn⟩ := h
  have hs := hp.scr_fits
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movm
    (VG.Proof.Sha512.X86.ea_of (B := VG.Proof.Argon2.X86.HPrime.scr s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), b.ebx])
      outOff)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, b.rd, b.wr]
        exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₃ u₃ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.esp]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.ebx]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, b.ebx]
  · rw [u₃.gpr, u₂.mem, u₁.mem]; exact hk
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hn]

theorem copy_rel {s₀ s₀' : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.X86.HPrime.Pre s₀') (q : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀') {k n : Nat} :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.CopyIn s₀ k n t₁ ∧ VG.Proof.Argon2.X86.HPrime.CopyIn s₀' k n t₂) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.ebx, h₂.1.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun s h => VG.Proof.Argon2.X86.HPrime.copy_blk hp h) (fun s h => VG.Proof.Argon2.X86.HPrime.copy_blk hp' h)) ?_
  exact RelCT.taint (A := taint) (τr [.esp, .ebx, .edx, .edi, .esi])
    (fun t₁ t₂ ⟨⟨a₁, b₁, c₁, d₁, e₁⟩, ⟨a₂, b₂, c₂, d₂, e₂⟩⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a₁, a₂, q.esp]
      · rw [b₁, b₂, q.scr_eq]
      · rw [c₁, c₂, q.scr_eq]
      · rw [d₁, d₂, q.op_eq]
      · rw [e₁, e₂]) (by taint_decide)

/-- Steps that keep memory, the permissions, `ebx` and `esp` keep the body. -/
theorem Body.same {s₀ s t : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) (hb : t.gpr .ebx = s.gpr .ebx)
    (he : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    VG.Proof.Argon2.X86.HPrime.Body s₀ t :=
  ⟨hb.trans b.ebx, he.trans b.esp, hrd.trans b.rd, hwr.trans b.wr, hm ▸ b.frame,
    fun q hq => hm ▸ b.saved q hq, hm ▸ b.pfx⟩

/-- The body, with `L` output bytes written. -/
def OutAt (s₀ : State) (L : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.X86.HPrime.Body s₀ s ∧ ∃ xs, VG.Proof.Argon2.X86.HPrime.Out s₀ s xs ∧ xs.length = L

theorem emit_blk {s₀ : State} {L : Nat} {s : State} (h : VG.Proof.Argon2.X86.HPrime.OutAt s₀ L s) :
    WP isa (.block [.mov .esi (.imm 32)]) s (VG.Proof.Argon2.X86.HPrime.CopyIn s₀ L 32) := by
  obtain ⟨b, xs, o, hx⟩ := h
  refine wp_movi fun s₁ u₁ => WP.block_nil ⟨b.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
    u₁.mem u₁.rd u₁.wr, ?_, u₁.gpr⟩
  show _ = _; rw [u₁.mem, ← hx]; exact o.ptr

theorem emit_rel {s₀ s₀' : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.X86.HPrime.Pre s₀') (q : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀') {L : Nat}
    (hL : L + 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.OutAt s₀ L t₁ ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀' L t₂) emitPrefix fun _ _ => True := by
  have hL' : L + 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀' := by rw [q.ol_eq]; exact hL
  have cp : ∀ {s₀ : State}, VG.Proof.Argon2.X86.HPrime.Pre s₀ → L + 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ → ∀ s, VG.Proof.Argon2.X86.HPrime.CopyIn s₀ L 32 s → WP isa copy s (VG.Proof.Argon2.X86.HPrime.Body s₀) :=
    fun hp hL s ⟨b, k, n⟩ => (VG.Proof.Argon2.X86.HPrime.copy_ok hp b k n (by decide) (by decide) hL).mono fun _ h => h.1
  unfold emitPrefix
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.X86.HPrime.emit_blk h) (fun _ h => VG.Proof.Argon2.X86.HPrime.emit_blk h))
    (RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_wp (VG.Proof.Argon2.X86.HPrime.copy_rel hp hp' q) (cp hp hL) (cp hp' hL')) ?_)
  exact RelCT.taint (A := taint) (τr [.esp, .ebx])
    (fun t₁ t₂ ⟨b₁, b₂⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [b₁.esp, b₂.esp, q.esp]
      · rw [b₁.ebx, b₂.ebx, q.scr_eq]) (by taint_decide)

theorem rem_blk {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) {L : Nat} {s : State} (h : VG.Proof.Argon2.X86.HPrime.OutAt s₀ L s) :
    WP isa (.block [.mov .esi (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) s
      (VG.Proof.Argon2.X86.HPrime.CopyIn s₀ L (VG.Proof.Argon2.X86.HPrime.ol s₀ - L)) := by
  obtain ⟨b, xs, o, hx⟩ := h
  have hs := hp.scr_fits
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff)
    (by rw [b.rd, b.wr]; exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₁ u₁ => WP.block_nil ⟨b.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
      u₁.mem u₁.rd u₁.wr, ?_, ?_⟩
  · show _ = _; rw [u₁.mem, ← hx]; exact o.ptr
  · rw [u₁.gpr, o.left, hx]

theorem copyRemaining_rel {s₀ s₀' : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.X86.HPrime.Pre s₀') (q : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.OutAt s₀ L t₁ ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀' L t₂) copyRemaining fun _ _ => True := by
  unfold copyRemaining
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.ebx, h₂.1.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.X86.HPrime.rem_blk hp h) (fun _ h => VG.Proof.Argon2.X86.HPrime.rem_blk hp' h)) ?_
  rw [q.ol_eq]
  exact VG.Proof.Argon2.X86.HPrime.copy_rel hp hp' q

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the output from the first digest, in two runs

`finishOutput_rel`: two runs with the same public data take the same
branches (the output length decides them) and the same number of chain
iterations, and write the output through the same addresses.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput copyRemaining
  leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_movm contains_addr)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

/-- `ChainInv`, for some digest `V`. -/
def ChainAt (s₀ : State) (e : BitVec 32) (j : Nat) (s : State) : Prop :=
  ∃ V : List Byte, V.length = 64 ∧ VG.Proof.Argon2.X86.HPrime.ChainInv s₀ e V j s

theorem ChainAt.outAt {s₀ : State} {e : BitVec 32} {j : Nat} {s : State} (h : VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j s) :
    VG.Proof.Argon2.X86.HPrime.OutAt s₀ (32 + 32 * j) s :=
  let ⟨_, hV, i⟩ := h
  ⟨i.body, _, i.out, VG.Proof.Argon2.X86.HPrime.chainOut_length hV j⟩

theorem cf_true {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some true) : p := by
  have e' : t.cf = some true := e
  rw [h] at e'; simpa using e'

theorem cf_false {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some false) : ¬ p := by
  have e' : t.cf = some false := e
  rw [h] at e'; simpa using e'

/-- The two runs agree on `esp` and `ebx`. -/
theorem agree_body {s₀ s₀' : State} (q : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀') {t₁ t₂ : State} (b₁ : VG.Proof.Argon2.X86.HPrime.Body s₀ t₁)
    (b₂ : VG.Proof.Argon2.X86.HPrime.Body s₀' t₂) : ∀ r ∈ [Reg.esp, .ebx], t₁.gpr r = t₂.gpr r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [b₁.esp, b₂.esp, q.esp]
  · rw [b₁.ebx, b₂.ebx, q.scr_eq]

section
variable {s₀ s₀' : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.X86.HPrime.Pre s₀') (q : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀')

/-! ## `next`, keeping the output -/

include hp in
theorem next_out_ok {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) {s : State}
    (h : VG.Proof.Argon2.X86.HPrime.InitIn (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) n s ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀ L s) : WP isa next s (VG.Proof.Argon2.X86.HPrime.OutAt s₀ L) := by
  obtain ⟨⟨c, e⟩, b, xs, o, hx⟩ := h
  exact (VG.Proof.Argon2.X86.HPrime.next_ok c e hn₁ hn₂).mono fun t ⟨_, k⟩ => ⟨b.keeps hp k, xs, o.keeps hp k, hx⟩

include hp hp' q in
theorem next_out_rel {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun t₁ t₂ => (VG.Proof.Argon2.X86.HPrime.InitIn (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) n t₁ ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀ L t₁) ∧
      (VG.Proof.Argon2.X86.HPrime.InitIn (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) n t₂ ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀' L t₂)) next
      fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.OutAt s₀ L t₁ ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀' L t₂ :=
  VG.Proof.Argon2.X86.HPrime.rel_wp ((VG.Proof.Argon2.X86.HPrime.next_rel hn₁ hn₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (fun _ h => VG.Proof.Argon2.X86.HPrime.next_out_ok hp hn₁ hn₂ h)
    (fun _ h => VG.Proof.Argon2.X86.HPrime.next_out_ok hp' hn₁ hn₂ ⟨by rw [q.scr_eq, q.esp]; exact h.1, h.2⟩)

/-! ## The chain -/

include hp in
/-- Setting `edx` keeps the body and the output. -/
theorem edx_blk {L n : Nat} {s : State} (h : VG.Proof.Argon2.X86.HPrime.OutAt s₀ L s) :
    WP isa (.block [.mov .edx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      VG.Proof.Argon2.X86.HPrime.InitIn (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) n t ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀ L t := by
  obtain ⟨b, xs, o, hx⟩ := h
  refine wp_movi fun s₁ u₁ => WP.block_nil ?_
  have b₁ := b.same (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  exact ⟨⟨b₁.ctx hp, u₁.gpr⟩, b₁, xs, o.same u₁.mem, hx⟩

include hp in
theorem emit_body {L : Nat} (hL : L + 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) {s : State} (h : VG.Proof.Argon2.X86.HPrime.OutAt s₀ L s) :
    WP isa emitPrefix s (VG.Proof.Argon2.X86.HPrime.Body s₀) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact (VG.Proof.Argon2.X86.HPrime.emit_ok hp b o (by rw [hx]; exact hL)).mono fun _ h => h.1

include hp hp' q in
/-- One iteration of the chain. -/
theorem body_rel {j : Nat} (hl : 32 + 32 * j + 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) {e e' : BitVec 32} :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j t₁ ∧ VG.Proof.Argon2.X86.HPrime.ChainAt s₀' e' j t₂)
      (.seq (.block [.mov .edx (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      fun _ _ => True := by
  have hl' : 32 + 32 * j + 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀' := by rw [q.ol_eq]; exact hl
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.X86.HPrime.edx_blk (n := 64) hp h.outAt)
    (fun _ h => (VG.Proof.Argon2.X86.HPrime.edx_blk (n := 64) hp' h.outAt).mono fun _ h => ⟨by rw [← q.scr_eq, ← q.esp]; exact h.1, h.2⟩))
    (RelCT.seq (VG.Proof.Argon2.X86.HPrime.next_out_rel hp hp' q (by decide) (by decide))
      (RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_wp (VG.Proof.Argon2.X86.HPrime.emit_rel hp hp' q hl) (fun _ h => VG.Proof.Argon2.X86.HPrime.emit_body hp hl h)
        (fun _ h => VG.Proof.Argon2.X86.HPrime.emit_body hp' hl' h)) ?_))
  exact RelCT.taint (A := taint) (τr [.esp, .ebx])
    (fun _ _ h => agree_regs (VG.Proof.Argon2.X86.HPrime.agree_body q h.1 h.2)) (by taint_decide)

/-- What the chain leaves: `j` iterations, and 33 to 64 bytes left. -/
def ChainDone (s₀ s₀' : State) (e e' : BitVec 32) (t₁ t₂ : State) : Prop :=
  ∃ j, VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j t₁ ∧ VG.Proof.Argon2.X86.HPrime.ChainAt s₀' e' j t₂ ∧ 33 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) ∧
    VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ VG.Proof.Argon2.X86.HPrime.ol s₀

include hp hp' q in
theorem chain_rel {e e' : BitVec 32} :
    RelCT isa (fun t₁ t₂ => ∃ j, 65 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) ∧ VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j t₁ ∧ VG.Proof.Argon2.X86.HPrime.ChainAt s₀' e' j t₂)
      chain (VG.Proof.Argon2.X86.HPrime.ChainDone s₀ s₀' e e') := by
  have ho := q.ol_eq
  refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, h65, h₁, h₂⟩ e₁ e₂ =>
    RelCT.loop (M := isa) (Q := VG.Proof.Argon2.X86.HPrime.ChainDone s₀ s₀' e e')
      (fun m t₁ t₂ => ∃ j, m = VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) ∧ 65 ≤ m ∧ VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j t₁ ∧ VG.Proof.Argon2.X86.HPrime.ChainAt s₀' e' j t₂)
      (fun m => ?_) _ s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, rfl, h65, h₁, h₂⟩ e₁ e₂
  refine RelCT.of_pre fun _ _ ⟨j, hm, h65, _, _⟩ => ?_
  subst hm
  have it := (VG.Proof.Argon2.X86.HPrime.body_rel hp hp' q (j := j) (by omega) (e := e) (e' := e')).wp
    (F₁ := fun (t : State) => VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e (j + 1) t ∧ t.cf = some (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * (j + 1)) < 65)))
    (F₂ := fun (t : State) => VG.Proof.Argon2.X86.HPrime.ChainAt s₀' e' (j + 1) t ∧ t.cf = some (decide (VG.Proof.Argon2.X86.HPrime.ol s₀' - (32 + 32 * (j + 1)) < 65)))
    fun t₁ t₂ ⟨⟨V, hV, i₁⟩, ⟨V', hV', i₂⟩⟩ =>
      ⟨(VG.Proof.Argon2.X86.HPrime.iter_ok hp hV i₁ (by omega)).mono fun _ h => ⟨⟨V, hV, h.1⟩, h.2⟩,
       (VG.Proof.Argon2.X86.HPrime.iter_ok hp' hV' i₂ (by omega)).mono fun _ h => ⟨⟨V', hV', h.1⟩, h.2⟩⟩
  refine it.mono (fun t₁ t₂ ⟨j', hj, _, a₁, a₂⟩ => ?_) fun t₁ t₂ ⟨_, ⟨c₁, f₁⟩, ⟨c₂, f₂⟩⟩ => ?_
  · have : j' = j := by omega
    subst this; exact ⟨a₁, a₂⟩
  · rw [ho] at f₂
    have ev : isa.eval .ae t₁ = isa.eval .ae t₂ := by
      show t₁.cf.map (!·) = t₂.cf.map (!·); rw [f₁, f₂]
    refine ⟨ev, fun hf => ?_, fun ht => ?_⟩
    · have : VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * (j + 1)) < 65 := by
        have hf' : t₁.cf.map (!·) = some false := hf
        rw [f₁] at hf'; simpa using hf'
      exact ⟨j + 1, c₁, c₂, by omega, by omega, by omega⟩
    · have : ¬ VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * (j + 1)) < 65 := by
        have ht' : t₁.cf.map (!·) = some true := ht
        rw [f₁] at ht'; simpa using ht'
      exact ⟨_, by omega, j + 1, rfl, by omega, c₁, c₂⟩

/-! ## Extending the digest -/

/-- The state `finishOutput` starts from. -/
def ExtIn (s₀ s : State) : Prop := VG.Proof.Argon2.X86.HPrime.Body s₀ s ∧ VG.Proof.Argon2.X86.HPrime.Out s₀ s [] ∧ s.gpr .ebp = s₀.gpr .ebp

include hp in
theorem ext_emit {s : State} (h : VG.Proof.Argon2.X86.HPrime.ExtIn s₀ s) (hol : 32 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) :
    WP isa emitPrefix s (VG.Proof.Argon2.X86.HPrime.ChainAt s₀ (s₀.gpr .ebp) 0) := by
  obtain ⟨b, o, e⟩ := h
  refine (VG.Proof.Argon2.X86.HPrime.emit_ok hp b o (by simp only [List.length_nil]; omega)).mono fun t ⟨bt, et, ot, dt⟩ =>
    ⟨VG.Proof.Argon2.X86.HPrime.digest s₀ s, by simp [VG.Proof.Argon2.X86.HPrime.digest, bytesAt], bt, et.trans e, ?_, ?_⟩
  · rw [List.nil_append] at ot
    simpa [VG.Proof.Argon2.X86.HPrime.chainOut, chainPrefixes] using ot
  · exact dt

include hp in
theorem ChainAt.keeps {e : BitVec 32} {j : Nat} {s t : State} (h : VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j s)
    (k : VG.Proof.Argon2.X86.HPrime.Keeps (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) s t) (m : t.mem = s.mem) : VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j t :=
  let ⟨V, hV, i⟩ := h
  ⟨V, hV, i.body.keeps hp k, k.ebp.trans i.ebp, i.out.keeps hp k,
    by show bytesAt _ _ _ = _; rw [m]; exact i.digest⟩

include hp in
theorem chain_cmp {e : BitVec 32} {j : Nat} {s : State} (h : VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j s) :
    WP isa (.block cmpLeft) s fun t => VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j t ∧
      t.cf = some (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j) < 65)) := by
  obtain ⟨V, hV, i⟩ := h
  refine (VG.Proof.Argon2.X86.HPrime.cmp_ok hp i.body i.out).mono fun t ⟨cf, k, m⟩ => ⟨ChainAt.keeps hp ⟨V, hV, i⟩ k m, ?_⟩
  rw [cf, VG.Proof.Argon2.X86.HPrime.chainOut_length hV]

include hp in
theorem left_blk {e : BitVec 32} {j : Nat} {s : State} (h : VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) s fun t =>
      VG.Proof.Argon2.X86.HPrime.InitIn (VG.Proof.Argon2.X86.HPrime.scr s₀) (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j)) t ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀ (32 + 32 * j) t := by
  obtain ⟨b, xs, o, hx⟩ := h.outAt
  have hs := hp.scr_fits
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff)
    (by rw [b.rd, b.wr]; exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₁ u₁ => WP.block_nil ?_
  have b₁ := b.same (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  exact ⟨⟨b₁.ctx hp, by rw [u₁.gpr, o.left, hx]⟩, b₁, xs, o.same u₁.mem, hx⟩

/-- `L` bytes written, and at most 64 left. -/
def Last (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ L, VG.Proof.Argon2.X86.HPrime.OutAt s₀ L t₁ ∧ VG.Proof.Argon2.X86.HPrime.OutAt s₀' L t₂ ∧ L < VG.Proof.Argon2.X86.HPrime.ol s₀ ∧ VG.Proof.Argon2.X86.HPrime.ol s₀ - L ≤ 64

include hp hp' q in
theorem last_rel {e e' : BitVec 32} :
    RelCT isa (VG.Proof.Argon2.X86.HPrime.ChainDone s₀ s₀' e e')
      (.seq (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) next) (VG.Proof.Argon2.X86.HPrime.Last s₀ s₀') := by
  have ho := q.ol_eq
  refine RelCT.of_pre fun _ _ ⟨j, _, _, l₁, l₂, l₃⟩ => ?_
  refine (RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.ebx] (F₁ := VG.Proof.Argon2.X86.HPrime.ChainAt s₀ e j) (F₂ := VG.Proof.Argon2.X86.HPrime.ChainAt s₀' e' j)
      (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        obtain ⟨_, _, i₁⟩ := h₁; obtain ⟨_, _, i₂⟩ := h₂
        rw [i₁.body.ebx, i₂.body.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
      (fun _ h => VG.Proof.Argon2.X86.HPrime.left_blk hp h)
      (fun _ h => (VG.Proof.Argon2.X86.HPrime.left_blk hp' h).mono fun _ h => ⟨by rw [← q.scr_eq, ← q.esp, ← ho]; exact h.1, h.2⟩))
    (VG.Proof.Argon2.X86.HPrime.next_out_rel hp hp' q (n := VG.Proof.Argon2.X86.HPrime.ol s₀ - (32 + 32 * j)) (by omega) l₂)).mono ?_ ?_
  · intro t₁ t₂ ⟨j', c₁, c₂, m₁, m₂, m₃⟩
    have : j' = j := by omega
    subst this; exact ⟨c₁, c₂⟩
  · intro t₁ t₂ ⟨o₁, o₂⟩
    exact ⟨_, o₁, o₂, by omega, by omega⟩

include hp hp' q in
theorem extend_rel (hol : 65 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀) :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.ExtIn s₀ t₁ ∧ VG.Proof.Argon2.X86.HPrime.ExtIn s₀' t₂) extendDigest (VG.Proof.Argon2.X86.HPrime.Last s₀ s₀') := by
  have ho := q.ol_eq
  have hol' : 65 ≤ VG.Proof.Argon2.X86.HPrime.ol s₀' := by rw [ho]; exact hol
  unfold extendDigest
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_wp ((VG.Proof.Argon2.X86.HPrime.emit_rel hp hp' q (L := 0) (by omega)).mono
      (fun _ _ ⟨⟨b₁, o₁, _⟩, ⟨b₂, o₂, _⟩⟩ => ⟨⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩⟩) fun _ _ h => h)
      (fun _ h => VG.Proof.Argon2.X86.HPrime.ext_emit hp h (by omega)) (fun _ h => VG.Proof.Argon2.X86.HPrime.ext_emit hp' h (by omega))) ?_
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx] (fun _ _ ⟨_, _, i₁⟩ ⟨_, _, i₂⟩ => VG.Proof.Argon2.X86.HPrime.agree_body q i₁.body i₂.body)
    ⟨_, by taint_decide⟩ (fun _ h => VG.Proof.Argon2.X86.HPrime.chain_cmp hp h) (fun _ h => VG.Proof.Argon2.X86.HPrime.chain_cmp hp' h)) ?_
  refine RelCT.seq (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by
      show t₁.cf = t₂.cf; rw [f₁, f₂, ho])
    (RelCT.nil fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, ht⟩ => ⟨0, c₁, c₂, by have := VG.Proof.Argon2.X86.HPrime.cf_true f₁ ht; omega⟩)
    ((VG.Proof.Argon2.X86.HPrime.chain_rel hp hp' q).mono (fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, hf⟩ =>
      ⟨0, by have := VG.Proof.Argon2.X86.HPrime.cf_false f₁ hf; omega, c₁, c₂⟩) fun _ _ h => h))
    (VG.Proof.Argon2.X86.HPrime.last_rel hp hp' q)


include hp in
theorem ext_cmp {s : State} (h : VG.Proof.Argon2.X86.HPrime.ExtIn s₀ s) :
    WP isa (.block cmpLeft) s fun t => VG.Proof.Argon2.X86.HPrime.ExtIn s₀ t ∧ t.cf = some (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ < 65)) := by
  obtain ⟨b, o, e⟩ := h
  refine (VG.Proof.Argon2.X86.HPrime.cmp_ok hp b o).mono fun t ⟨cf, k, _⟩ => ⟨⟨b.keeps hp k, o.keeps hp k, k.ebp.trans e⟩, ?_⟩
  rw [cf]; simp

include hp hp' q in
theorem finishOutput_rel :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.ExtIn s₀ t₁ ∧ VG.Proof.Argon2.X86.HPrime.ExtIn s₀' t₂) finishOutput fun _ _ => True := by
  have ho := q.ol_eq
  have hpos := hp.ol_pos
  unfold finishOutput
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx] (fun _ _ ⟨b₁, _⟩ ⟨b₂, _⟩ => VG.Proof.Argon2.X86.HPrime.agree_body q b₁ b₂)
    ⟨_, by taint_decide⟩ (fun _ h => VG.Proof.Argon2.X86.HPrime.ext_cmp hp h) (fun _ h => VG.Proof.Argon2.X86.HPrime.ext_cmp hp' h)) ?_
  refine RelCT.seq (R := VG.Proof.Argon2.X86.HPrime.Last s₀ s₀') (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by
      show t₁.cf = t₂.cf; rw [f₁, f₂, ho])
    (RelCT.nil fun _ _ ⟨⟨⟨⟨b₁, o₁, _⟩, f₁⟩, ⟨⟨b₂, o₂, _⟩, _⟩⟩, ht⟩ =>
      ⟨0, ⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩, by have := VG.Proof.Argon2.X86.HPrime.cf_true f₁ ht; omega,
        by have := VG.Proof.Argon2.X86.HPrime.cf_true f₁ ht; omega⟩)
    (RelCT.of_pre fun _ _ ⟨⟨⟨_, f₁⟩, _⟩, hf⟩ => (VG.Proof.Argon2.X86.HPrime.extend_rel hp hp' q (by have := VG.Proof.Argon2.X86.HPrime.cf_false f₁ hf; omega)).mono
      (fun _ _ ⟨⟨⟨e₁, _⟩, ⟨e₂, _⟩⟩, _⟩ => ⟨e₁, e₂⟩) fun _ _ h => h)) ?_
  exact RelCT.mono (RelCT.exists_ fun L => (VG.Proof.Argon2.X86.HPrime.copyRemaining_rel hp hp' q (L := L)).mono
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ h => h) (fun _ _ ⟨L, h⟩ => ⟨L, h⟩) fun _ _ h => h


end

end VG.Proof.Argon2.X86.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified`. -/
section

section

/-!
# Argon2 H′ on x86 (32-bit): correctness

`setup_ok` saves the caller's registers and lays out the output pointer, the
bytes left and the length prefix in `scratch`; `correct` composes it with
`first_ok`, `finish_ok` and the restore of the registers.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (setup restore first finishOutput saved outOff leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store readW_writeW_addr contains_addr)
open VG.Proof.Sha512.X86 (ea_of)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀)
include hp

theorem arg_in_rd {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * i)) 4 := by
  refine ⟨VG.Proof.Argon2.X86.HPrime.argR s₀, by simp [hrd, hp.rd], ?_⟩
  show Region.Contains ⟨addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * 0), 20⟩ _ _
  rw [VG.Proof.Argon2.X86.HPrime.arg_addr hp hi, VG.Proof.Argon2.X86.HPrime.arg_addr hp (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arg_frame {m : Mem} (f : Frame [VG.Proof.Argon2.X86.HPrime.scrR s₀] s₀.mem m) {i : Nat} (hi : i < 5) :
    m.readW (addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * i)) 32 = VG.X86.arg s₀ i := by
  refine f.readW (r := ⟨addr (VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (4 + 4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.arg_scr.sub_left (VG.Proof.Argon2.X86.HPrime.arg_sub hp hi)

theorem scr_in {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 16384) :
    InRegions s.wr (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 4 := by
  rw [hwr, hp.wr]
  exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp, contains_addr hd (by decide) hp.scr_fits⟩

theorem scr_frame {m : Mem} (f : Frame [VG.Proof.Argon2.X86.HPrime.scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 16384)
    (v : BitVec 32) : Frame [VG.Proof.Argon2.X86.HPrime.scrR s₀] s₀.mem (m.writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) v) :=
  f.writeW (List.mem_singleton_self _) v (contains_addr hd (by decide) hp.scr_fits)

/-- The state after `setup`. -/
theorem setup_ok : WP isa (.block setup) s₀ fun t => VG.Proof.Argon2.X86.HPrime.Body s₀ t ∧ VG.Proof.Argon2.X86.HPrime.Out s₀ t [] ∧
    t.gpr .ebp = s₀.gpr .ebp ∧ Frame [VG.Proof.Argon2.X86.HPrime.scrR s₀] s₀.mem t.mem := by
  have hs := hp.scr_fits
  have esp : s₀.gpr .esp = VG.Proof.Argon2.X86.HPrime.esp₀ s₀ := rfl
  unfold setup
  simp only [saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_movm (ea_of esp 20) (VG.Proof.Argon2.X86.HPrime.arg_in_rd hp (i := 4) rfl (by decide)) fun t₁ u₁ => ?_
  have a₁ : t₁.gpr .eax = VG.Proof.Argon2.X86.HPrime.scr s₀ := u₁.gpr
  refine wp_store (ea_of a₁ 840) (VG.Proof.Argon2.X86.HPrime.scr_in hp u₁.wr (by decide)) fun t₂ u₂ => ?_
  have a₂ : t₂.gpr .eax = VG.Proof.Argon2.X86.HPrime.scr s₀ := by rw [u₂.gpr, a₁]
  refine wp_store (ea_of a₂ 844) (VG.Proof.Argon2.X86.HPrime.scr_in hp (by rw [u₂.wr, u₁.wr]) (by decide)) fun t₃ u₃ => ?_
  have a₃ : t₃.gpr .eax = VG.Proof.Argon2.X86.HPrime.scr s₀ := by rw [u₃.gpr, a₂]
  refine wp_store (ea_of a₃ 848) (VG.Proof.Argon2.X86.HPrime.scr_in hp (by rw [u₃.wr, u₂.wr, u₁.wr]) (by decide)) fun t₄ u₄ => ?_
  refine wp_mov fun t₅ u₅ => ?_
  have b₅ : t₅.gpr .ebx = VG.Proof.Argon2.X86.HPrime.scr s₀ := by rw [u₅.gpr, u₄.gpr, a₃]
  have g₅ : ∀ r, r ≠ .ebx → r ≠ .eax → t₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₅.other _ h1, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ h2]
  have rd₅ : t₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : t₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have F₅ : Frame [VG.Proof.Argon2.X86.HPrime.scrR s₀] s₀.mem t₅.mem := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact VG.Proof.Argon2.X86.HPrime.scr_frame hp (VG.Proof.Argon2.X86.HPrime.scr_frame hp (VG.Proof.Argon2.X86.HPrime.scr_frame hp (by rw [u₁.mem]; exact Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _
  refine wp_movm (ea_of (by rw [g₅ _ (by decide) (by decide)]) 12)
    (VG.Proof.Argon2.X86.HPrime.arg_in_rd hp (i := 2) (by rw [rd₅]) (by decide)) fun t₆ u₆ => ?_
  refine wp_store (ea_of (by rw [u₆.other _ (by decide), b₅]) outOff)
    (VG.Proof.Argon2.X86.HPrime.scr_in hp (by rw [u₆.wr, wr₅]) (by decide)) fun t₇ u₇ => ?_
  refine wp_movm (ea_of (by rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide) (by decide)]) 16)
    (VG.Proof.Argon2.X86.HPrime.arg_in_rd hp (i := 3) (by rw [u₇.rd, u₆.rd, rd₅]) (by decide)) fun t₈ u₈ => ?_
  refine wp_store (ea_of (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]) leftOff)
    (VG.Proof.Argon2.X86.HPrime.scr_in hp (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅]) (by decide)) fun t₉ u₉ => ?_
  refine wp_store (ea_of (by rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]) 832)
    (VG.Proof.Argon2.X86.HPrime.scr_in hp (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]) (by decide)) fun t u => WP.block_nil ?_
  -- Values.
  have v₆ : t₆.gpr .eax = VG.Proof.Argon2.X86.HPrime.op s₀ := by rw [u₆.gpr, VG.Proof.Argon2.X86.HPrime.arg_frame hp F₅ (i := 2) (by decide)]
  have F₇ : Frame [VG.Proof.Argon2.X86.HPrime.scrR s₀] s₀.mem t₇.mem := by
    rw [u₇.mem, u₆.mem]; exact VG.Proof.Argon2.X86.HPrime.scr_frame hp F₅ (by decide) _
  have v₈ : t₈.gpr .eax = VG.X86.arg s₀ 3 := by rw [u₈.gpr, VG.Proof.Argon2.X86.HPrime.arg_frame hp F₇ (i := 3) (by decide)]
  have rds : t.rd = s₀.rd := by rw [u.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wrs : t.wr = s₀.wr := by rw [u.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  have gt : ∀ r, r ≠ .ebx → r ≠ .eax → t.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u.gpr, u₉.gpr, u₈.other _ h2, u₇.gpr, u₆.other _ h2, g₅ _ h1 h2]
  have bt : t.gpr .ebx = VG.Proof.Argon2.X86.HPrime.scr s₀ := by
    rw [u.gpr, u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]
  have m₉ : t₉.mem = (t₇.mem.writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) (VG.X86.arg s₀ 3)) := by
    rw [u₉.mem, u₈.mem, v₈]
  have mt : t.mem = (t₇.mem.writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) leftOff) (VG.X86.arg s₀ 3)).writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) 832)
      (VG.X86.arg s₀ 3) := by
    rw [u.mem, m₉, u₉.gpr, v₈]
  have m₇ : t₇.mem = t₅.mem.writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) outOff) (VG.Proof.Argon2.X86.HPrime.op s₀) := by
    rw [u₇.mem, u₆.mem, v₆]
  have Ft : Frame [VG.Proof.Argon2.X86.HPrime.scrR s₀] s₀.mem t.mem := by
    rw [mt]; exact VG.Proof.Argon2.X86.HPrime.scr_frame hp (VG.Proof.Argon2.X86.HPrime.scr_frame hp F₇ (by decide) _) (by decide) _
  -- Reads of `scratch` after the last writes.
  have R : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 16384 → e + 4 ≤ 16384 →
      (d + 4 ≤ e ∨ e + 4 ≤ d) →
      (m.writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) e) v).readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 = m.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 :=
    fun m v d e hd he h => readW_writeW_addr m v (by omega) (by omega) h
  have keep7 : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ 832 ∨ 864 ≤ d ∨ (836 ≤ d ∧ d + 4 ≤ 856)) →
      t.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 = t₅.mem.readW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 32 := fun d hd h => by
    rw [mt, R _ _ d 832 hd (by decide) (by omega), R _ _ d leftOff hd (by decide) (by simp only [leftOff]; omega),
      m₇, R _ _ d outOff hd (by decide) (by simp only [outOff]; omega)]
  have m₅ : t₅.mem = ((s₀.mem.writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) 840) (s₀.gpr .ebx)).writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) 844)
      (s₀.gpr .esi)).writeW (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) 848) (s₀.gpr .edi) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide)]
  refine ⟨⟨bt, by rw [gt _ (by decide) (by decide)], rds, wrs,
      Ft.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, fun q hq => ?_, ?_⟩,
    ⟨?_, ?_, rfl, Nat.zero_le _⟩, gt _ (by decide) (by decide), Ft⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [keep7 _ (by decide) (by decide), m₅, R _ _ 840 848 (by decide) (by decide) (by decide),
        R _ _ 840 844 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · rw [keep7 _ (by decide) (by decide), m₅, R _ _ 844 848 (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]
    · rw [keep7 _ (by decide) (by decide), m₅, Mem.readW_writeW_self32]
  · rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), show VG.Proof.Argon2.X86.HPrime.P s₀ + 832 = addr (VG.Proof.Argon2.X86.HPrime.scr s₀) 832 from
      (VG.Proof.Argon2.X86.HPrime.scr_addr hp (d := 832) (by decide)).symm, mt, Mem.readW_writeW_self32, Spec.Argon2.le32,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · show _ = _
    rw [mt, R _ _ outOff 832 (by decide) (by decide) (by decide),
      R _ _ outOff leftOff (by decide) (by decide) (by decide), m₇, Mem.readW_writeW_self32]
    simp
  · rw [mt, R _ _ leftOff 832 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    simp [VG.Proof.Argon2.X86.HPrime.ol]

theorem scr_rd {s : State} (b : VG.Proof.Argon2.X86.HPrime.Body s₀ s) {d : Nat} (hd : d + 4 ≤ 16384) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.HPrime.scr s₀) d) 4 := by
  rw [b.rd, b.wr]
  exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr hd (by decide) hp.scr_fits⟩

theorem correct : WP isa Impl.Argon2.X86.HPrime.code s₀ fun t => abiPreserved s₀ t ∧ hPrimeX86.post s₀ t := by
  have hif := hp.in_fits
  unfold Impl.Argon2.X86.HPrime.code
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.setup_ok hp).mono fun s₁ ⟨b₁, o₁, e₁, F₁⟩ => ?_)
  have hin : bytesAt s₁.mem ((VG.Proof.Argon2.X86.HPrime.inp s₀).setWidth 64) (VG.Proof.Argon2.X86.HPrime.inl s₀) = bytesAt s₀.mem ((VG.Proof.Argon2.X86.HPrime.inp s₀).setWidth 64) (VG.Proof.Argon2.X86.HPrime.inl s₀) :=
    Proof.Blake2.bytesAt_congr fun i hi => F₁.bytes (R := VG.Proof.Argon2.X86.HPrime.inR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.first_ok hp ⟨b₁, o₁, e₁, hin⟩).mono fun s₂ ⟨⟨b₂, o₂, e₂, _⟩, d₂⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.HPrime.finish_ok hp b₂ o₂ d₂).mono fun s₃ ⟨b₃, e₃, h₃⟩ => ?_)
  unfold restore
  refine wp_movm (ea_of b₃.ebx 848) (VG.Proof.Argon2.X86.HPrime.scr_rd hp b₃ (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (ea_of (by rw [u₄.other _ (by decide), b₃.ebx]) 844)
    (by rw [u₄.rd, u₄.wr]; exact VG.Proof.Argon2.X86.HPrime.scr_rd hp b₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_movm (ea_of (by rw [u₅.other _ (by decide), u₄.other _ (by decide), b₃.ebx]) 840)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact VG.Proof.Argon2.X86.HPrime.scr_rd hp b₃ (by decide)) fun t u => WP.block_nil ?_
  have mt : t.mem = s₃.mem := by rw [u.mem, u₅.mem, u₄.mem]
  have sv := b₃.saved
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at sv
  obtain ⟨sb, ss, sd⟩ := sv
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u.gpr, u₅.mem, u₄.mem]; exact sb
    · rw [u.other _ (by decide), u₅.gpr, u₄.mem]; exact ss
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; exact sd
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃, e₂]
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b₃.esp]
  · rw [mt]
    refine b₃.frame.readW (r := VG.Proof.Argon2.X86.HPrime.retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_out
    · exact hp.ret_scr
    · show Region.Disjoint _ ⟨(VG.Proof.Argon2.X86.HPrime.esp₀ s₀ - BitVec.ofNat 32 60).setWidth 64, 60⟩
      rw [Taint.sub_setWidth hp.esp_lo]
      exact Offset.base_disjoint_below _ (by omega)
  · show bytesAt t.mem _ _ = _
    rw [mt]; exact h₃

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): verified

Constant time, by relating two runs with the same public data piece by piece
(`code_ct`): the setup is checked by the taint analysis from the arguments,
`first` and `finishOutput` by their pieces; then `hPrime_verified` against the
contract with the arguments read only, and `hPrimeShared_verified` against
`Spec.Argon2.hPrimeContract`, which lets the code write them.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (setup restore first finishOutput chooseLength absorbInput finishInput
  absorbFixed leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movm wp_cmpi contains_addr)

/-! ## The setup -/

/-- The taint analysis of the setup starts with the stack arguments public,
and the word holding `scratch` known to be the base of the second writable
region. -/
def τS : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 16384], argLen := 24, argBases := [(20, 1)] }

theorem wfS {s : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s) : VG.X86.Taint.Wf VG.Proof.Argon2.X86.HPrime.τS s := by
  have ho := hp.out_fits; have hsc := hp.scr_fits; have hs := hp.esp_hi
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Argon2.X86.HPrime.τS], by simpa [hp.wr] using hp.out_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.arg_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [VG.Proof.Argon2.X86.HPrime.τS, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]

theorem agreeS {s₁ s₂ : State} (hp₁ : VG.Proof.Argon2.X86.HPrime.Pre s₁) (hp₂ : VG.Proof.Argon2.X86.HPrime.Pre s₂) (q : VG.Proof.Argon2.X86.HPrime.Same s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Argon2.X86.HPrime.τS s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Argon2.X86.HPrime.wfS hp₁, VG.Proof.Argon2.X86.HPrime.wfS hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => q.esp.symm,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Argon2.X86.HPrime.τS, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact q.esp.symm
  · rw [hp₁.wr, hp₂.wr]
    simp only [VG.Proof.Argon2.X86.HPrime.outR, VG.Proof.Argon2.X86.HPrime.scrR, VG.Proof.Argon2.X86.HPrime.P, VG.Proof.Argon2.X86.HPrime.op, VG.Proof.Argon2.X86.HPrime.ol, VG.Proof.Argon2.X86.HPrime.scr, q.args 2 (by decide), q.args 3 (by decide),
      q.args 4 (by decide)]
  · simp only [VG.Proof.Argon2.X86.HPrime.τS] at hk
    rw [show VG.X86.Taint.depth τS.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.esp_hi; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.esp_hi; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (q.args _ (by omega)).symm

theorem setup_F0 {s₀ : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) : WP isa (.block setup) s₀ (VG.Proof.Argon2.X86.HPrime.F0 s₀) := by
  have hif := hp.in_fits
  refine (VG.Proof.Argon2.X86.HPrime.setup_ok hp).mono fun t ⟨b, o, e, f⟩ => ⟨b, o, e, ?_⟩
  exact Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := VG.Proof.Argon2.X86.HPrime.inR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi

theorem setup_rel {s₀ s₀' : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.X86.HPrime.Pre s₀') (q : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀') :
    RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') (.block setup) fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.F0 s₀ t₁ ∧ VG.Proof.Argon2.X86.HPrime.F0 s₀' t₂ :=
  ((RelCT.taint (A := taint) VG.Proof.Argon2.X86.HPrime.τS (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact VG.Proof.Argon2.X86.HPrime.agreeS hp hp' q)
    (by taint_decide)).wp fun _ _ ⟨e₁, e₂⟩ =>
      ⟨by subst e₁; exact VG.Proof.Argon2.X86.HPrime.setup_F0 hp, by subst e₂; exact VG.Proof.Argon2.X86.HPrime.setup_F0 hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## `first` -/

section
variable {s₀ s₀' : State} (hp : VG.Proof.Argon2.X86.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.X86.HPrime.Pre s₀') (q : VG.Proof.Argon2.X86.HPrime.Same s₀ s₀')

include hp in
theorem choose_blk {s : State} (h : VG.Proof.Argon2.X86.HPrime.F0 s₀ s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff)), .alu .cmp .edx (.imm 65)]) s
      fun t => t.cf = some (decide (VG.Proof.Argon2.X86.HPrime.ol s₀ < 65)) := by
  have hs := hp.scr_fits
  have hol : VG.Proof.Argon2.X86.HPrime.ol s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  refine wp_movm (VG.Proof.Sha512.X86.ea_of h.body.ebx leftOff)
    (by rw [h.body.rd, h.body.wr]
        exact ⟨VG.Proof.Argon2.X86.HPrime.scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩) fun s₁ u₁ =>
    wp_cmpi fun s₂ _ cf₂ _ => WP.block_nil ?_
  rw [cf₂, u₁.gpr, h.out.left, List.length_nil, Nat.sub_zero,
    Proof.Sha256.X86.Stream.toNat_ofNat_lt hol]; rfl

include hp hp' q in
theorem choose_rel :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.F0 s₀ t₁ ∧ VG.Proof.Argon2.X86.HPrime.F0 s₀' t₂) chooseLength fun _ _ => True := by
  unfold chooseLength
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.body.ebx, h₂.body.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.X86.HPrime.choose_blk hp h) (fun _ h => VG.Proof.Argon2.X86.HPrime.choose_blk hp' h)) ?_
  exact RelCT.ite (fun t₁ t₂ ⟨f₁, f₂⟩ => by show t₁.cf = t₂.cf; rw [f₁, f₂, q.ol_eq])
    (RelCT.nil fun _ _ _ => trivial)
    (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => nomatch h) (by taint_decide))

include hp hp' q in
theorem first_rel :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.F0 s₀ t₁ ∧ VG.Proof.Argon2.X86.HPrime.F0 s₀' t₂) first fun t₁ t₂ =>
      (VG.Proof.Argon2.X86.HPrime.F0 s₀ t₁ ∧ (VG.Proof.Argon2.X86.HPrime.digest s₀ t₁).take (VG.Proof.Argon2.X86.HPrime.nF s₀) = Spec.Argon2.H (VG.Proof.Argon2.X86.HPrime.nF s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀) ++ VG.Proof.Argon2.X86.HPrime.inB s₀)) ∧
      (VG.Proof.Argon2.X86.HPrime.F0 s₀' t₂ ∧ (VG.Proof.Argon2.X86.HPrime.digest s₀' t₂).take (VG.Proof.Argon2.X86.HPrime.nF s₀') =
        Spec.Argon2.H (VG.Proof.Argon2.X86.HPrime.nF s₀') (Spec.Argon2.le32 (VG.Proof.Argon2.X86.HPrime.ol s₀') ++ VG.Proof.Argon2.X86.HPrime.inB s₀')) := by
  have hs := hp.scr_fits
  have hif := hp.in_fits
  have nE : VG.Proof.Argon2.X86.HPrime.nF s₀' = VG.Proof.Argon2.X86.HPrime.nF s₀ := by simp only [VG.Proof.Argon2.X86.HPrime.nF, q.ol_eq]
  unfold first
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_wp (VG.Proof.Argon2.X86.HPrime.choose_rel hp hp' q) (fun _ h => VG.Proof.Argon2.X86.HPrime.first_choose hp h)
    (fun _ h => VG.Proof.Argon2.X86.HPrime.first_choose hp' h)) ?_
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_wp ((VG.Proof.Argon2.X86.HPrime.init_rel (B := VG.Proof.Argon2.X86.HPrime.scr s₀) (E := VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (n := VG.Proof.Argon2.X86.HPrime.nF s₀) (VG.Proof.Argon2.X86.HPrime.nF_pos hp)
      (Nat.min_le_right _ _)).mono (fun _ _ ⟨⟨f₁, e₁⟩, ⟨f₂, e₂⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, e₁⟩, by
          have c := f₂.body.ctx hp'
          rw [q.scr_eq, q.esp] at c
          exact ⟨c, by rw [e₂, nE]⟩⟩) fun _ _ h => h)
    (fun _ h => VG.Proof.Argon2.X86.HPrime.first_init hp h) (fun _ h => VG.Proof.Argon2.X86.HPrime.first_init hp' h)) ?_
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_wp ((VG.Proof.Argon2.X86.HPrime.absorbFixed_rel (B := VG.Proof.Argon2.X86.HPrime.scr s₀) (E := VG.Proof.Argon2.X86.HPrime.esp₀ s₀) (offset := 832) (size := 4)
      (by omega) (by decide) (by decide) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide)))
      VG.Proof.Argon2.X86.HPrime.fixed_check_832).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, VG.Proof.Argon2.X86.HPrime.pfx_cov hp f₁.body⟩, by
          have c := f₂.body.ctx hp'
          have v := VG.Proof.Argon2.X86.HPrime.pfx_cov hp' f₂.body
          simp only [VG.Proof.Argon2.X86.HPrime.P] at v
          rw [q.scr_eq, q.esp] at c; rw [q.scr_eq] at v
          exact ⟨c, v⟩⟩) fun _ _ h => h)
    (fun _ h => VG.Proof.Argon2.X86.HPrime.first_fixed hp h) (fun _ h => VG.Proof.Argon2.X86.HPrime.first_fixed hp' h)) ?_
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_wp ?_ (fun _ h => VG.Proof.Argon2.X86.HPrime.first_input hp h) (fun _ h => VG.Proof.Argon2.X86.HPrime.first_input hp' h))
    (VG.Proof.Argon2.X86.HPrime.rel_wp ?_ (fun _ h => VG.Proof.Argon2.X86.HPrime.first_finish hp h) (fun _ h => VG.Proof.Argon2.X86.HPrime.first_finish hp' h))
  · unfold absorbInput
    refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx] (fun _ _ h₁ h₂ => VG.Proof.Argon2.X86.HPrime.agree_body q h₁.1.body h₂.1.body)
      ⟨_, by taint_decide⟩ (fun _ h => (VG.Proof.Argon2.X86.HPrime.absorbInput_blk hp h.1).mono fun _ h => h.1)
      (fun _ h => (VG.Proof.Argon2.X86.HPrime.absorbInput_blk hp' h.1).mono fun _ h => by
        have h := h.1
        rw [q.scr_eq, q.esp, q.inp_eq, q.inl_eq] at h; exact h)) ?_
    exact VG.Proof.Argon2.X86.HPrime.update_rel hif (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in
  · unfold finishInput
    refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.rel_taint [.esp, .ebx] (fun _ _ h₁ h₂ => VG.Proof.Argon2.X86.HPrime.agree_body q h₁.1.body h₂.1.body)
      ⟨_, by taint_decide⟩ (fun _ h => (VG.Proof.Argon2.X86.HPrime.finishInput_blk hp h.1).mono fun _ h => h.1)
      (fun _ h => (VG.Proof.Argon2.X86.HPrime.finishInput_blk hp' h.1).mono fun _ h => by
        have h := h.1
        rw [q.scr_eq, q.esp, VG.Proof.Argon2.X86.HPrime.cntLo, VG.Proof.Argon2.X86.HPrime.cntHi, q.inl_eq] at h; exact h)) ?_
    exact VG.Proof.Argon2.X86.HPrime.finalize_rel

end

/-! ## Constant time -/

theorem code_ct : ConstantTime isa hPrimeX86.pre hPrimeX86.pub Impl.Argon2.X86.HPrime.code := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    fun s₀ s₀' t₁ t₂ r₁ r₂ ⟨h₀, h₀', hq⟩ e₁ e₂ => ?_
  have hp := VG.Proof.Argon2.X86.HPrime.pre_of s₀ h₀
  have hp' := VG.Proof.Argon2.X86.HPrime.pre_of s₀' h₀'
  have q := Same.of_pub hq
  suffices h : RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') Impl.Argon2.X86.HPrime.code fun _ _ => True from
    h s₀ s₀' t₁ t₂ r₁ r₂ ⟨rfl, rfl⟩ e₁ e₂
  unfold Impl.Argon2.X86.HPrime.code
  refine RelCT.seq (VG.Proof.Argon2.X86.HPrime.setup_rel hp hp' q) (RelCT.seq (VG.Proof.Argon2.X86.HPrime.first_rel hp hp' q)
    (RelCT.seq (R := fun t₁ t₂ => VG.Proof.Argon2.X86.HPrime.Body s₀ t₁ ∧ VG.Proof.Argon2.X86.HPrime.Body s₀' t₂) ?_ ?_))
  · exact VG.Proof.Argon2.X86.HPrime.rel_wp ((VG.Proof.Argon2.X86.HPrime.finishOutput_rel hp hp' q).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
      ⟨⟨f₁.body, f₁.out, f₁.ebp⟩, ⟨f₂.body, f₂.out, f₂.ebp⟩⟩) fun _ _ h => h)
      (fun _ ⟨f, d⟩ => (VG.Proof.Argon2.X86.HPrime.finish_ok hp f.body f.out d).mono fun _ h => h.1)
      (fun _ ⟨f, d⟩ => (VG.Proof.Argon2.X86.HPrime.finish_ok hp' f.body f.out d).mono fun _ h => h.1)
  · exact RelCT.taint (A := taint) (τr [.ebx]) (fun _ _ ⟨b₁, b₂⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [b₁.ebx, b₂.ebx, q.scr_eq]) (by taint_decide)


/-! ## A state satisfying the precondition -/

/-- Memory holding the arguments `0x1000, 1, 0x2000, 1, 0x10000` at `0x5004`. -/
def hSatMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500D then 0x20 else
  if a = 0x5010 then 1 else if a = 0x5016 then 1 else 0

def hSatState : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Argon2.X86.HPrime.hSatMem
  rd := [⟨0x1000, 1⟩, ⟨0x5004, 20⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩]

theorem hSat_pre : hPrimeX86.pre VG.Proof.Argon2.X86.HPrime.hSatState := by
  have a0 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatState 0 = 0x1000 := by decide
  have a1 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatState 1 = 1 := by decide
  have a2 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatState 2 = 0x2000 := by decide
  have a3 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatState 3 = 1 := by decide
  have a4 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatState 4 = 0x10000 := by decide
  have e : argAddr VG.Proof.Argon2.X86.HPrime.hSatState 0 = 0x5004 := by decide
  simp only [VG.Proof.Argon2.X86.HPrime.hPrimeX86, a0, a1, a2, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem hPrime_verified : Verified X86.target Impl.Argon2.X86.HPrime.code VG.Proof.Argon2.X86.HPrime.hPrimeX86 :=
  ⟨fun s hs => VG.Proof.Argon2.X86.HPrime.correct (VG.Proof.Argon2.X86.HPrime.pre_of s hs), VG.Proof.Argon2.X86.HPrime.code_ct, ⟨VG.Proof.Argon2.X86.HPrime.hSatState, VG.Proof.Argon2.X86.HPrime.hSat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `hPrimeX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def hPrimeWide : Contract X86.isa :=
  { VG.Proof.Argon2.X86.HPrime.hPrimeX86 with
    pre := fun s =>
      let input : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
      let out : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
      let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, 16384⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩
      s.rd = [input] ∧ s.wr = [out, scratch, args] ∧
      input.Disjoint out ∧ input.Disjoint scratch ∧ input.Disjoint args ∧ out.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      ret.Disjoint input ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
      stack.Disjoint input ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧ stack.Disjoint args ∧
      (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
      (VG.X86.arg s 4).toNat + 16384 ≤ 2 ^ 32 ∧ 60 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 4 + 20 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 1).toNat < 2 ^ 32 ∧ 1 ≤ (VG.X86.arg s 3).toNat ∧ (VG.X86.arg s 3).toNat < 2 ^ 32 }

/-- A state satisfying `hPrimeWide.pre`. -/
def hSatWide : State :=
  { VG.Proof.Argon2.X86.HPrime.hSatState with
                   rd := [⟨0x1000, 1⟩], wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩, ⟨0x5004, 20⟩] }

macro "hnarrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [hPrimeX86, hPrimeWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem hPrimeWide_verified : Verified X86.target Impl.Argon2.X86.HPrime.code VG.Proof.Argon2.X86.HPrime.hPrimeWide :=
  Verified.narrowTo VG.Proof.Argon2.X86.HPrime.hPrime_verified
    (fun s => [⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩, ⟨argAddr s 0, 20⟩])
    (fun s => [⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩, ⟨(VG.X86.arg s 4).setWidth 64, 16384⟩])
    (fun s h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀,
        h₂₁, h₂₂, h₂₃, h₂₄⟩ := h
      have e : (⟨((s.gpr .esp) - BitVec.ofNat 32 60).setWidth 64, 60⟩ : Region) =
          ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩ := by rw [Taint.sub_setWidth h₂₀]; rfl
      hnarrow
      refine ⟨trivial, trivial, h₄, h₆, h₇.symm, h₈.symm, h₁₀, h₁₁, ?_, ?_, ?_, h₁₇, h₁₈, h₁₉, h₂₀,
        by omega, h₂₃⟩
      · simp only [below]; rw [e]; exact h₁₃
      · simp only [below]; rw [e]; exact h₁₄
      · simp only [below]; rw [e]; exact h₁₅)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by hnarrow at h ⊢; exact h)
    (fun _ _ _ _ h => by hnarrow; exact h)
    ⟨VG.Proof.Argon2.X86.HPrime.hSatWide, by
      have a0 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatWide 0 = 0x1000 := by decide
      have a1 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatWide 1 = 1 := by decide
      have a2 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatWide 2 = 0x2000 := by decide
      have a3 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatWide 3 = 1 := by decide
      have a4 : VG.X86.arg VG.Proof.Argon2.X86.HPrime.hSatWide 4 = 0x10000 := by decide
      have e : argAddr VG.Proof.Argon2.X86.HPrime.hSatWide 0 = 0x5004 := by decide
      simp only [VG.Proof.Argon2.X86.HPrime.hPrimeWide, a0, a1, a2, a3, a4, e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem hPrime_implies : hPrimeWide.Implies (Spec.Argon2.hPrimeContract X86.abi 60) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, VG.Proof.Argon2.X86.HPrime.hPrimeWide, VG.Proof.Argon2.X86.HPrime.hPrimeX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [hSatWide, hSatState, hSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.Argon2.X86.HPrime.hSatWide

/-- The emitted function, against the shared contract. -/
theorem hPrimeShared_verified :
    Verified X86.target Impl.Argon2.X86.HPrime.code (Spec.Argon2.hPrimeContract X86.abi 60) :=
  hPrimeWide_verified.of_implies VG.Proof.Argon2.X86.HPrime.hPrime_implies

end VG.Proof.Argon2.X86.HPrime

end
