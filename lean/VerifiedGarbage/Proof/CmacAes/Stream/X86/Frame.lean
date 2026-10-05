import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Impl.CmacAes.Stream.X86
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.Call`. -/
section

section

/-!
# Streaming AES-CMAC on x86: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). The arguments are on the stack, from
`[esp + 4]` (cdecl); `count` takes the slots 2 (low word) and 3. Each call of
a CMAC function pushes its six arguments and the return address in the 28
bytes below `esp`, and the callee's call of `vg_aes_ctr32` uses 28 bytes below
that: 56 bytes (48 for `init`, whose calls take four arguments), which may not
overlap any buffer.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86

/-- The 64-bit `count` argument, in the slots 2 and 3 (low word first). -/
def countX86 (s : State) : BitVec 64 := VG.X86.arg s 3 ++ VG.X86.arg s 2

/-- `vg_cmac_aes_init(state, key, key_len, scratch)`. -/
def initX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, 304⟩
    let key : Region := ⟨(VG.X86.arg s 1).setWidth 64, (VG.X86.arg s 2).toNat⟩
    let scr : Region := ⟨(VG.X86.arg s 3).setWidth 64, 2304⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 48, 48⟩
    s.rd = [key, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint key ∧ stack.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 304 ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + (VG.X86.arg s 2).toNat ≤ 2 ^ 32 ∧
      (VG.X86.arg s 3).toNat + 2304 ≤ 2 ^ 32 ∧ 48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      ((VG.X86.arg s 2).toNat = 16 ∨ (VG.X86.arg s 2).toNat = 24 ∨ (VG.X86.arg s 2).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem ((VG.X86.arg s 0).setWidth 64) (Spec.Aes.bytesAt s.mem ((VG.X86.arg s 1).setWidth 64) (VG.X86.arg s 2).toNat) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_cmac_aes_absorb(state, rounds, count, data, len, scratch)`. -/
def absorbX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, 304⟩
    let data : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩
    let scr : Region := ⟨(VG.X86.arg s 6).setWidth 64, 2304⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 56, 56⟩
    s.rd = [data, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 304 ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat ≤ 2 ^ 32 ∧
      (VG.X86.arg s 6).toNat + 2304 ≤ 2 ^ 32 ∧ 56 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
      ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem ((VG.X86.arg s 0).setWidth 64) key msg →
      (VG.X86.arg s 1).toNat = Spec.Aes.rounds (key.length / 4) →
      VG.Proof.CmacAes.Stream.X86.countX86 s = BitVec.ofNat 64 msg.length → msg.length + (VG.X86.arg s 5).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem ((VG.X86.arg s 0).setWidth 64) key
        (msg ++ Spec.Aes.bytesAt s.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_cmac_aes_finish(state, rounds, count, out, scratch)`. -/
def finishX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, 304⟩
    let out : Region := ⟨(VG.X86.arg s 4).setWidth 64, 16⟩
    let scr : Region := ⟨(VG.X86.arg s 5).setWidth 64, 2304⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 56, 56⟩
    s.rd = [args] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 304 ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + 16 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 5).toNat + 2304 ≤ 2 ^ 32 ∧ 56 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem ((VG.X86.arg s 0).setWidth 64) key msg →
      (VG.X86.arg s 1).toNat = Spec.Aes.rounds (key.length / 4) →
      VG.Proof.CmacAes.Stream.X86.countX86 s = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 4).setWidth 64) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, VG.X86.arg s₁ i = VG.X86.arg s₂ i

end VG.Proof.CmacAes.Stream.X86

end

/-!
# Streaming AES-CMAC on x86: the calls

A call, in a frame of its arguments, of each function the streaming functions
call (`vg_aes_expand_key_scratch`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and
`vg_cmac_aes_finalize`), from its contract (`WP.callWith`): what it needs
(`…Args`: the registers pushed as its arguments, and the regions), what it
leaves (`…Post`, in terms of the memory before the call), and that two calls
with the same arguments and stack pointer leak the same (`…_rel`, by
`RelCT.callWith`). A call of a function of six arguments uses the 56 bytes
below `esp` (`push`, the return address and the callee's call of
`vg_aes_ctr32`); `vg_cmac_aes_subkeys`, of four, 48; `vg_aes_expand_key_scratch`,
which calls nothing, 20.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Proof.CmacAes.X86 (updateX86 subkeysX86 finalizeX86 update_wp subkeys_wp finalize_wp update_ct
  subkeys_ct finalize_ct toNat_rounds)

/-! ## The stack -/

/-- The registers `call6` pushes. -/
abbrev rs6 : List Reg := [.edi, .esi, .ebx, .edx, .ecx, .eax]

/-- The registers `call4` pushes. -/
abbrev rs4 : List Reg := [.ebx, .edx, .ecx, .eax]

theorem hrs6 : Reg.esp ∉ VG.Proof.CmacAes.Stream.X86.rs6 := by decide
theorem hrs4 : Reg.esp ∉ VG.Proof.CmacAes.Stream.X86.rs4 := by decide

/-- A callee's return address, `k + 4` bytes below `esp`. -/
theorem sub_ret {E : BitVec 32} {k b : Nat} (h : k + 4 ≤ b) (hb : b ≤ E.toNat) :
    Region.Sub ⟨(E - BitVec.ofNat 32 (k + 4)).setWidth 64, 4⟩ (below E b) := by
  have := below_inner (sp := E) (a := 4) (b := b) (k := k) (by omega) hb
  simp only [below] at this
  rwa [BitVec.sub_sub, ← BitVec.ofNat_add] at this

/-- A callee's stack, the `a` bytes below its stack pointer `E - k`. -/
theorem sub_stk {E : BitVec 32} {k a b : Nat} (h : k + a ≤ b) (hb : b ≤ E.toNat) :
    Region.Sub ⟨(E - BitVec.ofNat 32 k).setWidth 64 - BitVec.ofNat 64 a, a⟩ (below E b) := by
  rw [← Taint.sub_setWidth (by rw [sub_toNat (by omega)]; omega)]
  exact below_inner (by omega) hb

/-- The bytes of a region the stack does not overlap, from the state a call
is made in. -/
theorem entry_bytes {rs : List Reg} {s : State} (hfit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat)
    (hrs : Reg.esp ∉ rs) {b : Nat} (hb : 4 * rs.length + 4 ≤ b) (hb' : b ≤ (s.gpr .esp).toNat) {p : Addr}
    {n : Nat} (hd : (below (s.gpr .esp) b).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt (pushed rs s).callEntry.mem p n = Spec.Aes.bytesAt s.mem p n :=
  Proof.Cmac.bytesAt_frame (callEntry_frame hfit hrs) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left (below_sub hb hb')).symm) hn

theorem eq_ofNat {x : BitVec 32} {n : Nat} (h : x = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) : x.toNat = n := by
  rw [h, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

/-! ## The callees -/

theorem upd_nosp : NoSp (Impl.CmacAes.X86.update v.callee) := Proof.CmacAes.X86.update_nosp v
theorem upd_stack : stackUse (Impl.CmacAes.X86.update v.callee) = 28 := Proof.CmacAes.X86.update_stack v
theorem sub_nosp : NoSp (Impl.CmacAes.X86.subkeys v.callee) := Proof.CmacAes.X86.subkeys_nosp v
theorem sub_stack : stackUse (Impl.CmacAes.X86.subkeys v.callee) = 28 := Proof.CmacAes.X86.subkeys_stack v
theorem fin_nosp : NoSp (Impl.CmacAes.X86.finalize v.callee) := Proof.CmacAes.X86.finalize_nosp v
theorem fin_stack : stackUse (Impl.CmacAes.X86.finalize v.callee) = 28 := Proof.CmacAes.X86.finalize_stack v
theorem ek_nosp : NoSp v.expand.code := v.expandNosp
theorem ek_stack : stackUse v.expand.code = 0 := v.expandStack

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`, in `eax`, `ecx`, `edx`, `ebx`, `esi` and `edi`. -/
structure UArgs (s : State) (W C D S : BitVec 32) (R n : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  esi : s.gpr .esi = BitVec.ofNat 32 n
  edi : s.gpr .edi = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 56 ≤ (s.gpr .esp).toNat
  hn : 16 * n < 2 ^ 32
  wc : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨C.setWidth 64, 16⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  dc : (⟨D.setWidth 64, 16 * n⟩ : Region).Disjoint ⟨C.setWidth 64, 16⟩
  ds : (⟨D.setWidth 64, 16 * n⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  cs : (⟨C.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  bW : (below (s.gpr .esp) 56).Disjoint ⟨W.setWidth 64, 240⟩
  bD : (below (s.gpr .esp) 56).Disjoint ⟨D.setWidth 64, 16 * n⟩
  bC : (below (s.gpr .esp) 56).Disjoint ⟨C.setWidth 64, 16⟩
  bS : (below (s.gpr .esp) 56).Disjoint ⟨S.setWidth 64, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 240⟩, ⟨D.setWidth 64, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨C.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 56] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (C.setWidth 64) 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (W.setWidth 64) (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem (C.setWidth 64) 16) (Spec.Cmac.blocksAt s.mem (D.setWidth 64) 16 n)

/-- The regions `vg_cmac_aes_update` is called with. -/
abbrev uRd (E W D : BitVec 32) (n : Nat) : List Region :=
  [⟨W.setWidth 64, 240⟩, ⟨D.setWidth 64, 16 * n⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
abbrev uWr (C S : BitVec 32) : List Region := [⟨C.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩]

namespace UArgs
variable {s : State} {W C D S : BitVec 32} {R n : Nat} (h : VG.Proof.CmacAes.Stream.X86.UArgs s W C D S R n)
include h

theorem fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 0 = W ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 R ∧
    VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 2 = C ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 3 = D ∧
    VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 n ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.CmacAes.Stream.X86.hrs6 (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.esi, h.edi]

theorem callPre : CallPre updateX86 VG.Proof.CmacAes.Stream.X86.rs6 (VG.Proof.CmacAes.Stream.X86.uRd (s.gpr .esp) W D n) (VG.Proof.CmacAes.Stream.X86.uWr C S) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := VG.Proof.CmacAes.Stream.X86.eq_ofNat rfl (by have := h.hn; omega)
  have he := h.esp
  have eA : argAddr (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (24 + 4) := by
    rw [callEntry_esp']; rfl
  have bA : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 56) := below_sub (by omega) he
  have bR := VG.Proof.CmacAes.Stream.X86.sub_ret (E := s.gpr .esp) (k := 24) (b := 56) (by omega) he
  have bK := VG.Proof.CmacAes.Stream.X86.sub_stk (E := s.gpr .esp) (k := 24 + 4) (a := 28) (b := 56) (by omega) he
  refine ⟨?_, ?_, ?_⟩
  · simp only [updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR, hN]
    refine ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.bC.sub_left bA, h.bS.sub_left bA,
      h.bC.sub_left bR, h.bS.sub_left bR, h.bW.sub_left bK, h.bD.sub_left bK, h.bC.sub_left bK,
      h.bS.sub_left bK, h.fW, h.fC, h.fD, h.fS, ?_, ?_, h.rounds⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a k ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a k hi
    obtain ⟨r', hr', hc'⟩ := h.writes a k hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end UArgs

theorem upd_call {s : State} {W C D S : BitVec 32} {R n : Nat} (h : VG.Proof.CmacAes.Stream.X86.UArgs s W C D S R n) :
    WP isa (call6 ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86.update v.callee)) s (VG.Proof.CmacAes.Stream.X86.UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := VG.Proof.CmacAes.Stream.X86.eq_ofNat rfl (by have := h.hn; omega)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have he := h.esp
  refine WP.callWith (rs := VG.Proof.CmacAes.Stream.X86.rs6) (k := updateX86) (fun _ hs => update_wp v hs) (VG.Proof.CmacAes.Stream.X86.upd_nosp v) (by simp) VG.Proof.CmacAes.Stream.X86.hrs6
    (by rw [(VG.Proof.CmacAes.Stream.X86.upd_stack v)]; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  rw [(VG.Proof.CmacAes.Stream.X86.upd_stack v)] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  have keep : ∀ {p : BitVec 32} {k : Nat}, (below (s.gpr .esp) 56).Disjoint ⟨p.setWidth 64, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry.mem (p.setWidth 64) k = Spec.Aes.bytesAt s.mem (p.setWidth 64) k :=
    fun hd hk => VG.Proof.CmacAes.Stream.X86.entry_bytes h.fit VG.Proof.CmacAes.Stream.X86.hrs6 (by simp) he hd hk
  simp only [updateX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hN, m₂] at post
  rw [post, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq, Proof.CmacAes.X86.ciphAt,
    keep (h.bW.sub_right (Region.sub_prefix hRb)) (by omega), keep h.bC (by decide),
    keep h.bD (by have := h.hn; omega)]

theorem upd_rel {W C D S E : BitVec 32} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.X86.UArgs s₁ W C D S R n ∧ VG.Proof.CmacAes.Stream.X86.UArgs s₂ W C D S R n ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (call6 ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86.update v.callee)) fun _ _ => True := by
  refine RelCT.callWith (fun _ hs => update_wp v hs) (update_ct v) (VG.Proof.CmacAes.Stream.X86.uRd E W D n) (VG.Proof.CmacAes.Stream.X86.uWr C S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

/-! ## `vg_cmac_aes_finalize` -/

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`, in `eax`, `ecx`, `edx`, `ebx`, `esi` and `edi`. -/
structure FArgs (s : State) (K St P S : BitVec 32) (L R : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = St
  ebx : s.gpr .ebx = P
  esi : s.gpr .esi = BitVec.ofNat 32 L
  edi : s.gpr .edi = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  esp : 56 ≤ (s.gpr .esp).toNat
  kst : (⟨K.setWidth 64, 272⟩ : Region).Disjoint ⟨St.setWidth 64, 16⟩
  ks : (⟨K.setWidth 64, 272⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  pst : (⟨P.setWidth 64, L⟩ : Region).Disjoint ⟨St.setWidth 64, 16⟩
  ps : (⟨P.setWidth 64, L⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  sts : (⟨St.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  bK : (below (s.gpr .esp) 56).Disjoint ⟨K.setWidth 64, 272⟩
  bP : (below (s.gpr .esp) 56).Disjoint ⟨P.setWidth 64, L⟩
  bSt : (below (s.gpr .esp) 56).Disjoint ⟨St.setWidth 64, 16⟩
  bS : (below (s.gpr .esp) 56).Disjoint ⟨S.setWidth 64, 2176⟩
  fK : K.toNat + 272 ≤ 2 ^ 32
  fSt : St.toNat + 16 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨K.setWidth 64, 272⟩, ⟨P.setWidth 64, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨St.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 56] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (K.setWidth 64) (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K.setWidth 64 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem (St.setWidth 64) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (St.setWidth 64) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (P.setWidth 64) L)

/-- The regions `vg_cmac_aes_finalize` is called with. -/
abbrev fRd (E K P : BitVec 32) (L : Nat) : List Region :=
  [⟨K.setWidth 64, 272⟩, ⟨P.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
abbrev fWr (St S : BitVec 32) : List Region := [⟨St.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩]

namespace FArgs
variable {s : State} {K St P S : BitVec 32} {L R : Nat} (h : VG.Proof.CmacAes.Stream.X86.FArgs s K St P S L R)
include h

theorem fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 0 = K ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 R ∧
    VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 2 = St ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 3 = P ∧
    VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 L ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.CmacAes.Stream.X86.hrs6 (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.esi, h.edi]

theorem callPre : CallPre finalizeX86 VG.Proof.CmacAes.Stream.X86.rs6 (VG.Proof.CmacAes.Stream.X86.fRd (s.gpr .esp) K P L) (VG.Proof.CmacAes.Stream.X86.fWr St S) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := VG.Proof.CmacAes.Stream.X86.eq_ofNat rfl (by have := h.len; omega)
  have he := h.esp
  have eA : argAddr (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (24 + 4) := by
    rw [callEntry_esp']; rfl
  have bA : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 56) := below_sub (by omega) he
  have bR := VG.Proof.CmacAes.Stream.X86.sub_ret (E := s.gpr .esp) (k := 24) (b := 56) (by omega) he
  have bK := VG.Proof.CmacAes.Stream.X86.sub_stk (E := s.gpr .esp) (k := 24 + 4) (a := 28) (b := 56) (by omega) he
  refine ⟨?_, ?_, ?_⟩
  · simp only [finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR, hL]
    refine ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.bSt.sub_left bA, h.bS.sub_left bA,
      h.bSt.sub_left bR, h.bS.sub_left bR, h.bK.sub_left bK, h.bP.sub_left bK, h.bSt.sub_left bK,
      h.bS.sub_left bK, h.fK, h.fSt, h.fP, h.fS, ?_, ?_, h.rounds, h.len⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a k ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a k hi
    obtain ⟨r', hr', hc'⟩ := h.writes a k hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end FArgs

theorem fin_call {s : State} {K St P S : BitVec 32} {L R : Nat} (h : VG.Proof.CmacAes.Stream.X86.FArgs s K St P S L R) :
    WP isa (call6 ("vg_cmac_aes_finalize" ++ v.suffix) (Impl.CmacAes.X86.finalize v.callee)) s (VG.Proof.CmacAes.Stream.X86.FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := VG.Proof.CmacAes.Stream.X86.eq_ofNat rfl (by have := h.len; omega)
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h | h | h <;> omega
  have he := h.esp
  refine WP.callWith (rs := VG.Proof.CmacAes.Stream.X86.rs6) (k := finalizeX86) (fun _ hs => finalize_wp v hs) (VG.Proof.CmacAes.Stream.X86.fin_nosp v) (by simp) VG.Proof.CmacAes.Stream.X86.hrs6
    (by rw [(VG.Proof.CmacAes.Stream.X86.fin_stack v)]; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  rw [(VG.Proof.CmacAes.Stream.X86.fin_stack v)] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  have keep : ∀ {p : Addr} {k : Nat}, (below (s.gpr .esp) 56).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed VG.Proof.CmacAes.Stream.X86.rs6 s).callEntry.mem p k = Spec.Aes.bytesAt s.mem p k :=
    fun hd hk => VG.Proof.CmacAes.Stream.X86.entry_bytes h.fit VG.Proof.CmacAes.Stream.X86.hrs6 (by simp) he hd hk
  simp only [finalizeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hL, m₂] at post
  intro _ _ hk msg hm hne hst
  have eK := keep (h.bK.sub_right (Region.sub_prefix hRb)) (by omega)
  have eK2 := keep (p := K.setWidth 64 + 240) (k := 32)
    (h.bK.sub_right (Offset.sub_base (K.setWidth 64) (d := 240) (n := 32) (by decide))) (by decide)
  have eSt := keep h.bSt (by decide)
  have eP := keep h.bP (by omega)
  simp only [Proof.CmacAes.X86.ciphAt, eK, eK2, eSt, eP] at post
  exact post hk msg hm hne hst

theorem fin_rel {K St P S E : BitVec 32} {L R : Nat} {Q : State → State → Prop}
    (h : ∀ s₁ s₂, Q s₁ s₂ → VG.Proof.CmacAes.Stream.X86.FArgs s₁ K St P S L R ∧ VG.Proof.CmacAes.Stream.X86.FArgs s₂ K St P S L R ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa Q (call6 ("vg_cmac_aes_finalize" ++ v.suffix) (Impl.CmacAes.X86.finalize v.callee)) fun _ _ => True := by
  refine RelCT.callWith (fun _ hs => finalize_wp v hs) (finalize_ct v) (VG.Proof.CmacAes.Stream.X86.fRd E K P L) (VG.Proof.CmacAes.Stream.X86.fWr St S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

/-! ## `vg_cmac_aes_subkeys` -/

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`, in `eax`, `ecx`,
`edx` and `ebx`. -/
structure SArgs (s : State) (W K S : BitVec 32) (R : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = K
  ebx : s.gpr .ebx = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 48 ≤ (s.gpr .esp).toNat
  wk : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨K.setWidth 64, 32⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  ks : (⟨K.setWidth 64, 32⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  bW : (below (s.gpr .esp) 48).Disjoint ⟨W.setWidth 64, 240⟩
  bK : (below (s.gpr .esp) 48).Disjoint ⟨K.setWidth 64, 32⟩
  bS : (below (s.gpr .esp) 48).Disjoint ⟨S.setWidth 64, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fK : K.toNat + 32 ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨K.setWidth 64, 32⟩, ⟨S.setWidth 64, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨K.setWidth 64, 32⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 48] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (K.setWidth 64) 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (W.setWidth 64) (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (W.setWidth 64) (16 * (R + 1)))) 16).2

/-- The regions `vg_cmac_aes_subkeys` is called with. -/
abbrev sRd (E W : BitVec 32) : List Region :=
  [⟨W.setWidth 64, 240⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
abbrev sWr (K S : BitVec 32) : List Region := [⟨K.setWidth 64, 32⟩, ⟨S.setWidth 64, 2176⟩]

namespace SArgs
variable {s : State} {W K S : BitVec 32} {R : Nat} (h : VG.Proof.CmacAes.Stream.X86.SArgs s W K S R)
include h

theorem fit : 4 * rs4.length + 4 ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 0 = W ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 1 = BitVec.ofNat 32 R ∧
    VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 2 = K ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 3 = S := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.CmacAes.Stream.X86.hrs4 (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx]

theorem callPre : CallPre subkeysX86 VG.Proof.CmacAes.Stream.X86.rs4 (VG.Proof.CmacAes.Stream.X86.sRd (s.gpr .esp) W) (VG.Proof.CmacAes.Stream.X86.sWr K S) s := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hR := toNat_rounds h.rounds
  have he := h.esp
  have eA : argAddr (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (16 + 4) := by
    rw [callEntry_esp']; rfl
  have bA : Region.Sub (below (s.gpr .esp) 16) (below (s.gpr .esp) 48) := below_sub (by omega) he
  have bR := VG.Proof.CmacAes.Stream.X86.sub_ret (E := s.gpr .esp) (k := 16) (b := 48) (by omega) he
  have bK := VG.Proof.CmacAes.Stream.X86.sub_stk (E := s.gpr .esp) (k := 16 + 4) (a := 28) (b := 48) (by omega) he
  refine ⟨?_, ?_, ?_⟩
  · simp only [subkeysX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, hR]
    refine ⟨trivial, trivial, h.wk, h.ws, h.ks, h.bK.sub_left bA, h.bS.sub_left bA,
      h.bK.sub_left bR, h.bS.sub_left bR, h.bW.sub_left bK, h.bK.sub_left bK,
      h.bS.sub_left bK, h.fW, h.fK, h.fS, ?_, ?_, h.rounds⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a k ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a k hi
    obtain ⟨r', hr', hc'⟩ := h.writes a k hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end SArgs

theorem sub_call {s : State} {W K S : BitVec 32} {R : Nat} (h : VG.Proof.CmacAes.Stream.X86.SArgs s W K S R) :
    WP isa (call4 ("vg_cmac_aes_subkeys" ++ v.suffix) (Impl.CmacAes.X86.subkeys v.callee)) s (VG.Proof.CmacAes.Stream.X86.SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have he := h.esp
  refine WP.callWith (rs := VG.Proof.CmacAes.Stream.X86.rs4) (k := subkeysX86) (fun _ hs => subkeys_wp v hs) (VG.Proof.CmacAes.Stream.X86.sub_nosp v) (by simp) VG.Proof.CmacAes.Stream.X86.hrs4
    (by rw [(VG.Proof.CmacAes.Stream.X86.sub_stack v)]; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  rw [(VG.Proof.CmacAes.Stream.X86.sub_stack v)] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [subkeysX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hR, m₂] at post
  rw [post, Proof.CmacAes.X86.ciphAt,
    VG.Proof.CmacAes.Stream.X86.entry_bytes h.fit VG.Proof.CmacAes.Stream.X86.hrs4 (by simp) he (h.bW.sub_right (Region.sub_prefix hRb)) (by omega)]

theorem sub_rel {W K S E : BitVec 32} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.X86.SArgs s₁ W K S R ∧ VG.Proof.CmacAes.Stream.X86.SArgs s₂ W K S R ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (call4 ("vg_cmac_aes_subkeys" ++ v.suffix) (Impl.CmacAes.X86.subkeys v.callee)) fun _ _ => True := by
  refine RelCT.callWith (fun _ hs => subkeys_wp v hs) (subkeys_ct v) (VG.Proof.CmacAes.Stream.X86.sRd E W) (VG.Proof.CmacAes.Stream.X86.sWr K S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the key `Kp` of `KL` bytes,
the schedule `W` and the working space `S`, in `eax`, `ecx`, `edx` and
`ebx`. -/
structure EArgs (s : State) (Kp W S : BitVec 32) (KL : Nat) : Prop where
  eax : s.gpr .eax = Kp
  ecx : s.gpr .ecx = BitVec.ofNat 32 KL
  edx : s.gpr .edx = W
  ebx : s.gpr .ebx = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  esp : 20 ≤ (s.gpr .esp).toNat
  kw : (⟨Kp.setWidth 64, KL⟩ : Region).Disjoint ⟨W.setWidth 64, 240⟩
  ks : (⟨Kp.setWidth 64, KL⟩ : Region).Disjoint ⟨S.setWidth 64, 512⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 512⟩
  bK : (below (s.gpr .esp) 20).Disjoint ⟨Kp.setWidth 64, KL⟩
  bW : (below (s.gpr .esp) 20).Disjoint ⟨W.setWidth 64, 240⟩
  bS : (below (s.gpr .esp) 20).Disjoint ⟨S.setWidth 64, 512⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fW : W.toNat + 240 ≤ 2 ^ 32
  fS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨Kp.setWidth 64, KL⟩] (s.rd ++ s.wr)
  writes : Covers [⟨W.setWidth 64, 240⟩, ⟨S.setWidth 64, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure EPost (s : State) (Kp W S : BitVec 32) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨W.setWidth 64, 240⟩, ⟨S.setWidth 64, 512⟩, below (s.gpr .esp) 20] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W.setWidth 64) (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (Kp.setWidth 64) KL)

/-- The regions `vg_aes_expand_key_scratch` is called with. -/
abbrev eRd (E Kp : BitVec 32) (KL : Nat) : List Region :=
  [⟨Kp.setWidth 64, KL⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
abbrev eWr (W S : BitVec 32) : List Region := [⟨W.setWidth 64, 240⟩, ⟨S.setWidth 64, 512⟩]

namespace EArgs
variable {s : State} {Kp W S : BitVec 32} {KL : Nat} (h : VG.Proof.CmacAes.Stream.X86.EArgs s Kp W S KL)
include h

theorem fit : 4 * rs4.length + 4 ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 0 = Kp ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 1 = BitVec.ofNat 32 KL ∧
    VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 2 = W ∧ VG.X86.arg (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 3 = S := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.CmacAes.Stream.X86.hrs4 (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx]

theorem callPre : CallPre Proof.Aes.expandKeyX86 VG.Proof.CmacAes.Stream.X86.rs4 (VG.Proof.CmacAes.Stream.X86.eRd (s.gpr .esp) Kp KL) (VG.Proof.CmacAes.Stream.X86.eWr W S) s := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hK : (BitVec.ofNat 32 KL).toNat = KL := VG.Proof.CmacAes.Stream.X86.eq_ofNat rfl (by rcases h.klen with h | h | h <;> omega)
  have he := h.esp
  have eA : argAddr (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.CmacAes.Stream.X86.rs4 s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (16 + 4) := by
    rw [callEntry_esp']; rfl
  have bA : Region.Sub (below (s.gpr .esp) 16) (below (s.gpr .esp) 20) := below_sub (by omega) he
  have bR := VG.Proof.CmacAes.Stream.X86.sub_ret (E := s.gpr .esp) (k := 16) (b := 20) (by omega) he
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.expandKeyX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, hK]
    refine ⟨trivial, trivial, h.kw, h.ks, h.ws, h.bW.sub_left bA, h.bS.sub_left bA,
      h.bW.sub_left bR, h.bS.sub_left bR, h.fK, h.fW, h.fS, ?_, h.klen⟩
    rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a k ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a k hi
    obtain ⟨r', hr', hc'⟩ := h.writes a k hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end EArgs

theorem ek_call {s : State} {Kp W S : BitVec 32} {KL : Nat} (h : VG.Proof.CmacAes.Stream.X86.EArgs s Kp W S KL) :
    WP isa (call4 v.expand.name v.expand.code) s (VG.Proof.CmacAes.Stream.X86.EPost s Kp W S KL) := by
  have hK : (BitVec.ofNat 32 KL).toNat = KL := VG.Proof.CmacAes.Stream.X86.eq_ofNat rfl (by rcases h.klen with h | h | h <;> omega)
  have he := h.esp
  refine WP.callWith (rs := VG.Proof.CmacAes.Stream.X86.rs4) (k := Proof.Aes.expandKeyX86) v.expandOk (VG.Proof.CmacAes.Stream.X86.ek_nosp v)
    (by simp) VG.Proof.CmacAes.Stream.X86.hrs4 (by rw [(VG.Proof.CmacAes.Stream.X86.ek_stack v)]; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  rw [(VG.Proof.CmacAes.Stream.X86.ek_stack v)] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [Proof.Aes.expandKeyX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hK, m₂] at post
  rw [post, VG.Proof.CmacAes.Stream.X86.entry_bytes h.fit VG.Proof.CmacAes.Stream.X86.hrs4 (by simp) he h.bK (by rcases h.klen with h | h | h <;> omega)]

theorem ek_rel {Kp W S E : BitVec 32} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.X86.EArgs s₁ Kp W S KL ∧ VG.Proof.CmacAes.Stream.X86.EArgs s₂ Kp W S KL ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (call4 v.expand.name v.expand.code) fun _ _ => True := by
  refine RelCT.callWith v.expandOk v.expandCt (VG.Proof.CmacAes.Stream.X86.eRd E Kp KL) (VG.Proof.CmacAes.Stream.X86.eWr W S)
    fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

end VG.Proof.CmacAes.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.Common`. -/
section

/-!
# Streaming AES-CMAC on x86: arithmetic, copies and saved registers

The number of bytes held back, as the code computes it from `count`'s two
words (`held_ok`); the copy of `ecx` bytes from `esi` to `edi` (`copy_wp`);
and the registers saved in the scratch buffer (`slot_read`, `restore_wp`).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

open VG.WriteBytes

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd Mupd Fupd WP.cons wp_mov wp_movi wp_movm wp_store wp_addi wp_add wp_subi wp_sub
  wp_andi wp_cmp wp_test wp_movzx8 wp_store8 eval_e eval_ne eval_b ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacAes.X86 (wp_arg ea_at' byte_rt32 addr_at add0')
open VG.Proof.Cmac.Stream (held held_le held_pos held_zero)

/-! ## Arithmetic -/

theorem toNat_count (hi lo : BitVec 32) : (hi ++ lo).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt lo.isLt]

theorem zero_iff (x : BitVec 32) : x = 0#32 ↔ x.toNat = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩

/-- `or` of the two words of `count` is 0 exactly when `count` is. -/
theorem count_zero (hi lo : BitVec 32) : (hi ||| lo == 0) = decide ((hi ++ lo).toNat = 0) := by
  rw [VG.Proof.CmacAes.Stream.X86.toNat_count]
  have e : hi ||| lo = 0#32 ↔ hi.toNat * 2 ^ 32 + lo.toNat = 0 := by
    rw [BitVec.or_eq_zero_iff, VG.Proof.CmacAes.Stream.X86.zero_iff hi, VG.Proof.CmacAes.Stream.X86.zero_iff lo]; omega
  by_cases h : hi.toNat * 2 ^ 32 + lo.toNat = 0
  · simp only [h, decide_true, beq_iff_eq]; exact e.mpr h
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun h' => h (e.mp h')

theorem and15 (x : BitVec 32) : (x &&& 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero `count`, from its low word,
as `sub 1; and 15; add 1` computes it. -/
theorem held_lo {hi lo : BitVec 32} (h : (hi ++ lo).toNat ≠ 0) :
    ((lo - 1) &&& 15) + 1 = BitVec.ofNat 32 (held (hi ++ lo).toNat) := by
  rw [held_pos (by omega)]
  rw [VG.Proof.CmacAes.Stream.X86.toNat_count] at h ⊢
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, VG.Proof.CmacAes.Stream.X86.and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  have := lo.isLt
  omega

/-- For `count` 0, its low word is 0. -/
theorem held_lo0 {hi lo : BitVec 32} (h : (hi ++ lo).toNat = 0) : lo = BitVec.ofNat 32 (held (hi ++ lo).toNat) := by
  rw [h, held_zero]
  rw [VG.Proof.CmacAes.Stream.X86.toNat_count] at h
  exact (VG.Proof.CmacAes.Stream.X86.zero_iff lo).mpr (by omega)

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## One instruction at a time -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `or d, r`, with ZF. -/
theorem wp_orz {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → s'.zf = some (s.gpr d ||| s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _) rfl)

/-- `shr d, n`, as a division by `2 ^ n`. -/
theorem wp_shr' {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  MdStream.X86.wp_shr hn k

end

/-! ## The bytes held back -/

/-- `count0 r` then `held r` leave the bytes held back for `count` in `r`,
changing only `r`, `ecx` and the flags. -/
theorem held_ok {r : Reg} (hr : r ≠ .ecx) (hr' : r ≠ .esp) {s₀ s : State} {Q : State → Prop}
    (hesp : s.gpr .esp = s₀.gpr .esp)
    (h2 : InRegions (s.rd ++ s.wr) (argAddr s₀ 2) 4) (h3 : InRegions (s.rd ++ s.wr) (argAddr s₀ 3) 4)
    (v2 : s.mem.readW (argAddr s₀ 2) 32 = VG.X86.arg s₀ 2) (v3 : s.mem.readW (argAddr s₀ 3) 32 = VG.X86.arg s₀ 3)
    (k : ∀ s', s'.gpr r = BitVec.ofNat 32 (held (VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat) →
      (∀ q, q ≠ r → q ≠ .ecx → s'.gpr q = s.gpr q) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (countHeld r) s Q := by
  refine WP.seq (VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) hesp h2 v2 fun s₁ u₁ => ?_)
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₁.other _ (Ne.symm hr'), hesp]) (by rw [u₁.rd, u₁.wr]; exact h3)
    (by rw [u₁.mem]; exact v3) fun s₂ u₂ => VG.Proof.CmacAes.Stream.X86.wp_orz fun s₃ u₃ z₃ => WP.block_nil ?_
  have e₃ : s₃.gpr r = VG.X86.arg s₀ 2 := by rw [u₃.other _ hr, u₂.other _ hr, u₁.gpr]
  have z : s₃.zf = some (decide ((VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat = 0)) := by
    rw [z₃, u₂.gpr, u₂.other _ hr, u₁.gpr, VG.Proof.CmacAes.Stream.X86.countX86, VG.Proof.CmacAes.Stream.X86.count_zero]
  have g₃ : ∀ q, q ≠ r → q ≠ .ecx → s₃.gpr q = s.gpr q := fun q a b => by
    rw [u₃.other _ b, u₂.other _ b, u₁.other _ a]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have ev : isa.eval .e s₃ = some (decide ((VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat = 0)) := by
    show VG.X86.eval .e s₃ = _; rw [eval_e, z]
  by_cases h0 : (VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat = 0
  · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact k s₃ (by rw [e₃]; exact VG.Proof.CmacAes.Stream.X86.held_lo0 h0) g₃ m₃ rd₃ wr₃
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine wp_subi fun s₄ u₄ _ => wp_andi fun s₅ u₅ => wp_addi fun s₆ u₆ => WP.block_nil ?_
    refine k s₆ ?_ (fun q a b => by rw [u₆.other _ a, u₅.other _ a, u₄.other _ a, g₃ q a b])
      (by rw [u₆.mem, u₅.mem, u₄.mem, m₃]) (by rw [u₆.rd, u₅.rd, u₄.rd, rd₃]) (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃])
    rw [u₆.gpr, u₅.gpr, u₄.gpr, e₃]
    exact VG.Proof.CmacAes.Stream.X86.held_lo h0

/-! ## Copying bytes -/

/-- The copy loop, for `L` bytes (not 0). -/
theorem copyLoop_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L < 2 ^ 32)
    (hsi : s.gpr .esi = p) (hdi : s.gpr .edi = c) (hcx : s.gpr .ecx = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + L ≤ 2 ^ 32)
    (hr : Covers [⟨p.setWidth 64, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨c.setWidth 64, L⟩] s.wr)
    (hd : (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, L⟩) :
    WP isa Impl.CmacAes.X86.copy s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edi 0) .al,
      .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .esi = p + BitVec.ofNat 32 i ∧
      t.gpr .edi = c + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (L - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [hsi, add0'], by rw [hdi, add0'], by rw [hcx, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, xsi, xdi, xcx, mem, g, rd, wr⟩
  refine wp_movzx8 (a := p.setWidth 64 + BitVec.ofNat 64 i) (by rw [ea_at', xsi]; exact addr_at (by omega))
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_store8 (a := c.setWidth 64 + BitVec.ofNat 64 i)
    (by rw [ea_at', u₁.other _ (by decide), xdi]; exact addr_at (by omega))
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (p.setWidth 64) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i)
      (p.setWidth 64 + BitVec.ofNat 64 i) = s.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
    (VG.WriteBytes.writeBytes_frame s.mem (c.setWidth 64) _ (R := ⟨c.setWidth 64, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have al : t₁.gpr Reg8.al.reg = (t.mem (p.setWidth 64 + BitVec.ofNat 64 i)).setWidth 32 := u₁.gpr
  have hmem : t₅.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, al, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have cx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (L - i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xcx]
  have xcx' : t₅.gpr .ecx = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.X86.eval .ne t₅ = _
    rw [eval_ne, z₅, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
    rfl
  have gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t₅.gpr r = s.gpr r := fun r ha hc hs hd' => by
    rw [u₅.other _ hc, u₄.other _ hd', u₃.other _ hs, v₂.gpr, u₁.other _ ha, g r ha hc hs hd']
  have xdi' : t₅.gpr .edi = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xdi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have xsi' : t₅.gpr .esi = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), xsi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, xsi', xdi', xcx', hmem, gg,
      rd', wr'⟩

/-- `copy`: the `L` bytes at `p` (`esi`) copied to `c` (`edi`), none if `L`
(`ecx`) is 0. -/
theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL : L < 2 ^ 32)
    (hsi : s.gpr .esi = p) (hdi : s.gpr .edi = c) (hcx : s.gpr .ecx = BitVec.ofNat 32 L)
    (fp : 0 < L → p.toNat + L ≤ 2 ^ 32) (fc : 0 < L → c.toNat + L ≤ 2 ^ 32)
    (hr : 0 < L → Covers [⟨p.setWidth 64, L⟩] (s.rd ++ s.wr)) (hw : 0 < L → Covers [⟨c.setWidth 64, L⟩] s.wr)
    (hd : 0 < L → (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, L⟩) :
    WP isa copy s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have ev : isa.eval .e s₁ = some (decide (L = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, z₁, hcx, BitVec.and_self, ofNat_beq_zero hL]
  by_cases h0 : L = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [f₁.mem]; simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], fun r _ _ _ _ => by rw [f₁.gpr], f₁.rd, f₁.wr⟩
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    have h0' : 0 < L := by omega
    refine WP.mono (VG.Proof.CmacAes.Stream.X86.copyLoop_wp h0' hL (by rw [f₁.gpr]; exact hsi) (by rw [f₁.gpr]; exact hdi)
      (by rw [f₁.gpr]; exact hcx) (fp h0') (fc h0') (by rw [f₁.rd, f₁.wr]; exact hr h0')
      (by rw [f₁.wr]; exact hw h0') (hd h0'))
      fun s' ⟨m, g, rd, wr⟩ => ⟨by rw [m, f₁.mem], fun r a b c d => by rw [g r a b c d, f₁.gpr], by rw [rd, f₁.rd],
        by rw [wr, f₁.wr]⟩

/-! ## Bytes written -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    VG.WriteBytes.writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [VG.WriteBytes.writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (VG.WriteBytes.writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.CmacAes.Stream.X86.writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, VG.Proof.CmacAes.Stream.X86.bytesAt_writeBytes_self _ _ (by omega)]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact VG.WriteBytes.writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

/-! ## The saved registers -/

theorem saved_fits : Spill.Fits 2192 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2192 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

theorem save_eq : save = Spill.saveCode .eax saved := rfl

theorem restore_eq (i : Nat) : restore i = .mov .eax (argOp i) :: (Spill.restoreCode .eax saved ++ []) := rfl

/-- Each slot of `saved` holds the register saved there. -/
theorem saveMem_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (Spill.saveMem m (B + BitVec.ofNat 64 ·) g saved).readW (B + BitVec.ofNat 64 d) 32 = g r :=
  Spill.saveMem_saved_ofNat m B g VG.Proof.CmacAes.Stream.X86.saved_fits (by decide) (r, d) h

/-- The memory after saving the registers in the scratch buffer at `Sc`. -/
def savedMem (s₀ : State) (Sc : BitVec 32) : Mem :=
  Spill.saveMem s₀.mem (Sc.setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

theorem savedMem_frame (s₀ : State) (Sc : BitVec 32) :
    Frame [⟨Sc.setWidth 64 + BitVec.ofNat 64 2176, 16⟩] s₀.mem (VG.Proof.CmacAes.Stream.X86.savedMem s₀ Sc) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => by
    have h := VG.Proof.CmacAes.Stream.X86.saved_bound p hp
    rw [show Sc.setWidth 64 + BitVec.ofNat 64 p.2 =
        Sc.setWidth 64 + BitVec.ofNat 64 2176 + BitVec.ofNat 64 (p.2 - 2176) by
      rw [Offset.add_add, Nat.add_sub_cancel' h.1]]
    exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers, with the scratch buffer `Sc` in `eax`. -/
theorem save_wp {is : List Instr} {s : State} {Q : State → Prop} {Sc : BitVec 32} (heax : s.gpr .eax = Sc)
    (hfit : Sc.toNat + 2304 ≤ 2 ^ 32) (hw : Covers [⟨Sc.setWidth 64, 2304⟩] s.wr)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = Spill.saveMem s.mem (Sc.setWidth 64 + BitVec.ofNat 64 ·) s.gpr saved → WP isa (.block is) s' Q) :
    WP isa (.block (save ++ is)) s Q := by
  rw [VG.Proof.CmacAes.Stream.X86.save_eq]
  refine Spill.save_ofNat_ok saved VG.Proof.CmacAes.Stream.X86.saved_fits (by rw [heax]; omega) (fun p hp => ?_) fun s' u =>
    k s' u.gpr u.rd u.wr (by rw [u.mem, heax])
  have hb := VG.Proof.CmacAes.Stream.X86.saved_bound p hp
  rw [heax]
  exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩

/-- Restoring the registers, from the scratch buffer `Sc` (the stack argument
`i`), whose slots hold the registers of `s₀`. -/
theorem restore_wp {s₀ s : State} {i : Nat} {Sc : BitVec 32} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = Sc)
    (hfit : Sc.toNat + 2304 ≤ 2 ^ 32) (hr : Covers [⟨Sc.setWidth 64, 2304⟩] (s.rd ++ s.wr))
    (hs : ∀ r d, (r, d) ∈ saved → s.mem.readW (Sc.setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r) :
    WP isa (.block (restore i)) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  rw [VG.Proof.CmacAes.Stream.X86.restore_eq]
  refine VG.Proof.MdStream.X86.wp_movm (a := argAddr s₀ i) (by rw [ea_at', hesp]; rfl) hin fun s₁ u₁ => ?_
  rw [hv] at u₁
  refine Spill.restore_ofNat_ok saved VG.Proof.CmacAes.Stream.X86.saved_fits (by rw [u₁.gpr]; omega) VG.Proof.CmacAes.Stream.X86.saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact hs p.1 p.2 hp') fun s₂ r₂ =>
      WP.block_nil ⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), hesp]), by rw [r₂.mem, u₁.mem]⟩
  have hb := VG.Proof.CmacAes.Stream.X86.saved_bound p hp'
  rw [u₁.gpr, u₁.rd, u₁.wr]
  exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩

/-! ## The stack arguments and the stack -/

theorem argAddr_eq {s₀ : State} {n i : Nat} (hfit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hi : i < n) :
    argAddr s₀ i = (s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := addr_eq (by omega)

/-- Argument `i` among the `n`. -/
theorem arg_sub {s₀ : State} {n i : Nat} (hfit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hi : i < n) :
    Region.Sub ⟨argAddr s₀ i, 4⟩ ⟨argAddr s₀ 0, 4 * n⟩ := by
  rw [VG.Proof.CmacAes.Stream.X86.argAddr_eq hfit hi, VG.Proof.CmacAes.Stream.X86.argAddr_eq hfit (by omega : 0 < n),
    show 4 + 4 * i = (4 + 4 * 0) + 4 * i by omega, ← Offset.add_add]
  exact Offset.sub_base _ (by omega)

/-- The arguments are above the stack below `esp`. -/
theorem args_below {s₀ : State} {n k : Nat} (hfit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hn : 0 < n)
    (hk : k ≤ (s₀.gpr .esp).toNat) : (below (s₀.gpr .esp) k).Disjoint ⟨argAddr s₀ 0, 4 * n⟩ := by
  rw [VG.Proof.CmacAes.Stream.X86.argAddr_eq hfit hn]
  show Region.Disjoint ⟨(s₀.gpr .esp - BitVec.ofNat 32 k).setWidth 64, k⟩ _
  rw [Taint.sub_setWidth hk]
  exact Offset.disjoint_below_above _ (by omega)

/-- So is the return address. -/
theorem ret_below {E : BitVec 32} {k : Nat} (hk : k ≤ E.toNat) :
    (⟨E.setWidth 64, 4⟩ : Region).Disjoint (below E k) := by
  show Region.Disjoint _ ⟨(E - BitVec.ofNat 32 k).setWidth 64, k⟩
  rw [Taint.sub_setWidth hk]
  exact Offset.base_disjoint_below _ (by omega)

theorem below_eq {E : BitVec 32} {k : Nat} (hk : k ≤ E.toNat) :
    below E k = ⟨E.setWidth 64 - BitVec.ofNat 64 k, k⟩ := by
  simp only [below]; rw [Taint.sub_setWidth hk]

/-- An argument is unchanged where only regions disjoint from it change. -/
theorem arg_keep {s₀ : State} {rs : List Region} {m : Mem} (hf : Frame rs s₀.mem m) {i : Nat}
    (hd : ∀ r ∈ rs, (⟨argAddr s₀ i, 4⟩ : Region).Disjoint r) : m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem arg_ofNat (s₀ : State) (i : Nat) : VG.X86.arg s₀ i = BitVec.ofNat 32 (VG.X86.arg s₀ i).toNat := by simp

/-- `x + d`, as an address, for `x + d` within the 32-bit space. -/
theorem add_setWidth {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

theorem add_toNat {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).toNat = x.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega)]; exact Nat.mod_eq_of_lt h

theorem arg_contains {s₀ : State} {n i : Nat} (hfit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hi : i < n) :
    (⟨argAddr s₀ 0, 4 * n⟩ : Region).Contains (argAddr s₀ i) 4 := by
  have e : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
    rw [VG.Proof.CmacAes.Stream.X86.argAddr_eq hfit hi, VG.Proof.CmacAes.Stream.X86.argAddr_eq hfit (by omega : 0 < n), Offset.add_add]
  rewrite [e]
  exact Offset.contains_base _ (by omega) (by omega)

/-! ## Two runs between the calls -/

/-- What two runs agree on between the calls: `esp`, the writable regions
and the `n` stack arguments are those on entry. -/
structure Pt (n : Nat) (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  wr : s.wr = s₀.wr
  args : ∀ i < n, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i

theorem Pt.refl (n : Nat) (s₀ : State) : VG.Proof.CmacAes.Stream.X86.Pt n s₀ s₀ := ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Two runs at points with `Pt`, from entry states that agree on `esp` and
the arguments, agree on `esp`, the arguments and the registers `rs`. -/
theorem Pt.agree {n : Nat} {rs : List Reg} {s₀ s₀' s₁ s₂ : State} (hsp : s₀.gpr .esp = s₀'.gpr .esp)
    (hq : ∀ i < n, VG.X86.arg s₀ i = VG.X86.arg s₀' i) (o : ArgsOut n s₀) (o' : ArgsOut n s₀') (h₁ : VG.Proof.CmacAes.Stream.X86.Pt n s₀ s₁)
    (h₂ : VG.Proof.CmacAes.Stream.X86.Pt n s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * n)) s₁ s₂ := by
  have out : ∀ {t s : State}, ArgsOut n t → VG.Proof.CmacAes.Stream.X86.Pt n t s → ArgsOut n s := fun ⟨a, b⟩ h => by
    rw [ArgsOut, h.esp, h.wr]; exact ⟨a, b⟩
  have cur : ∀ {t s : State}, VG.Proof.CmacAes.Stream.X86.Pt n t s → ∀ i < n, VG.X86.arg s i = VG.X86.arg t i := fun {t s} h i hi => by
    show s.mem.readW (argAddr s i) 32 = _
    rw [show argAddr s i = argAddr t i by simp only [argAddr, h.esp]]; exact h.args i hi
  exact agree_argTaint hr (by rw [h₁.esp, h₂.esp, hsp]) (out o h₁) (out o' h₂)
    fun i hi => by rw [cur h₁ i hi, cur h₂ i hi, hq i hi]

end VG.Proof.CmacAes.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.AbsorbBlocks`. -/
section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb`'s straight-line code

The precondition by name (`APre`), what holds at every point of the code
outside the calls (`ACtx`: `esp`, the regions and the stack arguments are
those on entry), and what each piece of code between the copies and calls
computes, in terms of `count` (`c`) and `len` (`L`): the bytes held back `h =
held c`, the bytes copied after them `f = min L (16 - h)`, the data left `L -
f`, whether to chain the block held back (`b1`), the blocks chained after it
(`nb`), and the rest (`rest`).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd Fupd wp_mov wp_movi wp_addi wp_add wp_subi wp_sub wp_andi wp_cmp wp_shr eval_e
  eval_b ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacAes.X86 (wp_arg toNat_rounds)
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - VG.Proof.CmacAes.Stream.X86.fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if VG.Proof.CmacAes.Stream.X86.leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if VG.Proof.CmacAes.Stream.X86.leftOf c L = 0 then 0 else (VG.Proof.CmacAes.Stream.X86.leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := VG.Proof.CmacAes.Stream.X86.leftOf c L - 16 * VG.Proof.CmacAes.Stream.X86.nbOf c L

theorem f_le (c L : Nat) : VG.Proof.CmacAes.Stream.X86.fOf c L ≤ L ∧ VG.Proof.CmacAes.Stream.X86.fOf c L + held c ≤ 16 := by
  have := held_le c; unfold VG.Proof.CmacAes.Stream.X86.fOf; omega

theorem nb_le (c L : Nat) : VG.Proof.CmacAes.Stream.X86.fOf c L + 16 * VG.Proof.CmacAes.Stream.X86.nbOf c L + VG.Proof.CmacAes.Stream.X86.restOf c L = L := by
  have := VG.Proof.CmacAes.Stream.X86.f_le c L; unfold VG.Proof.CmacAes.Stream.X86.restOf VG.Proof.CmacAes.Stream.X86.nbOf VG.Proof.CmacAes.Stream.X86.leftOf; split <;> omega

theorem rest_le (c L : Nat) : VG.Proof.CmacAes.Stream.X86.restOf c L ≤ 16 := by unfold VG.Proof.CmacAes.Stream.X86.restOf VG.Proof.CmacAes.Stream.X86.nbOf VG.Proof.CmacAes.Stream.X86.leftOf; split <;> omega

theorem rest_zero {c L : Nat} (h : VG.Proof.CmacAes.Stream.X86.leftOf c L = 0) : VG.Proof.CmacAes.Stream.X86.restOf c L = 0 := by simp [VG.Proof.CmacAes.Stream.X86.restOf, VG.Proof.CmacAes.Stream.X86.nbOf, h]

/-! ## Arithmetic on registers -/

/-- `16 nb` for the data left `x > 0`, as `sub 1; mov; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 32) :
    BitVec.ofNat 32 x - 1 - ((BitVec.ofNat 32 x - 1) &&& 15) = BitVec.ofNat 32 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 32 x - 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]; omega
  rw [BitVec.toNat_sub, VG.Proof.CmacAes.Stream.X86.and15, e, BitVec.toNat_ofNat]
  omega

theorem shr4 {n : Nat} (hn : 16 * n < 2 ^ 32) :
    BitVec.ofNat 32 (16 * n) >>> 4 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev aSt : BitVec 32 := VG.X86.arg s₀ 0
abbrev aR : Nat := (VG.X86.arg s₀ 1).toNat
abbrev aD : BitVec 32 := VG.X86.arg s₀ 4
abbrev aL : Nat := (VG.X86.arg s₀ 5).toNat
abbrev aSc : BitVec 32 := VG.X86.arg s₀ 6
abbrev aE : BitVec 32 := s₀.gpr .esp
/-- `count`. -/
abbrev aC : Nat := (VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat
abbrev astR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64, 304⟩
abbrev adR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64, VG.Proof.CmacAes.Stream.X86.aL s₀⟩
abbrev ascR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64, 2304⟩
abbrev aaR : Region := ⟨argAddr s₀ 0, 28⟩

/-- Where the function writes: the state, the scratch buffer and the stack. -/
abbrev ABig : List Region := [VG.Proof.CmacAes.Stream.X86.astR s₀, VG.Proof.CmacAes.Stream.X86.ascR s₀, below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56]

end

/-- The precondition, by name. -/
structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.Stream.X86.adR s₀, VG.Proof.CmacAes.Stream.X86.aaR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.Stream.X86.astR s₀, VG.Proof.CmacAes.Stream.X86.ascR s₀]
  st_d : (VG.Proof.CmacAes.Stream.X86.astR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.adR s₀)
  st_s : (VG.Proof.CmacAes.Stream.X86.astR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.ascR s₀)
  d_s : (VG.Proof.CmacAes.Stream.X86.adR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.ascR s₀)
  a_st : (VG.Proof.CmacAes.Stream.X86.aaR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.astR s₀)
  a_s : (VG.Proof.CmacAes.Stream.X86.aaR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.ascR s₀)
  ret_st : (⟨(VG.Proof.CmacAes.Stream.X86.aE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.astR s₀)
  ret_s : (⟨(VG.Proof.CmacAes.Stream.X86.aE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.ascR s₀)
  b_st' : (⟨(VG.Proof.CmacAes.Stream.X86.aE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.astR s₀)
  b_d' : (⟨(VG.Proof.CmacAes.Stream.X86.aE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.adR s₀)
  b_s' : (⟨(VG.Proof.CmacAes.Stream.X86.aE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.ascR s₀)
  fSt : (VG.Proof.CmacAes.Stream.X86.aSt s₀).toNat + 304 ≤ 2 ^ 32
  fD : (VG.Proof.CmacAes.Stream.X86.aD s₀).toNat + VG.Proof.CmacAes.Stream.X86.aL s₀ ≤ 2 ^ 32
  fS : (VG.Proof.CmacAes.Stream.X86.aSc s₀).toNat + 2304 ≤ 2 ^ 32
  esp56 : 56 ≤ (VG.Proof.CmacAes.Stream.X86.aE s₀).toNat
  espfit : (VG.Proof.CmacAes.Stream.X86.aE s₀).toNat + 32 ≤ 2 ^ 32
  rounds : VG.Proof.CmacAes.Stream.X86.aR s₀ = 10 ∨ VG.Proof.CmacAes.Stream.X86.aR s₀ = 12 ∨ VG.Proof.CmacAes.Stream.X86.aR s₀ = 14

theorem APre.of {s₀ : State} (h : absorbX86.pre s₀) : VG.Proof.CmacAes.Stream.X86.APre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

namespace APre
variable {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀)
include hp

theorem b_st : (below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56).Disjoint (VG.Proof.CmacAes.Stream.X86.astR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp56]; exact hp.b_st'
theorem b_d : (below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56).Disjoint (VG.Proof.CmacAes.Stream.X86.adR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp56]; exact hp.b_d'
theorem b_s : (below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56).Disjoint (VG.Proof.CmacAes.Stream.X86.ascR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp56]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 7 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 7) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.CmacAes.Stream.X86.aaR s₀, by simp [hp.rd], VG.Proof.CmacAes.Stream.X86.arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `ABig` changes. -/
theorem keep {m : Mem} (hf : Frame (VG.Proof.CmacAes.Stream.X86.ABig s₀) s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  VG.Proof.CmacAes.Stream.X86.arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_st.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact (VG.Proof.CmacAes.Stream.X86.args_below hp.fit (by decide) hp.esp56).symm.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)

theorem argsOut : ArgsOut 7 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 28) (by have := hp.espfit; omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 28) (by have := hp.espfit; omega) hp.ret_s hp.a_s

end APre

theorem APre.lt {s₀ : State} (_hp : VG.Proof.CmacAes.Stream.X86.APre s₀) : VG.Proof.CmacAes.Stream.X86.aL s₀ < 2 ^ 32 := (VG.X86.arg s₀ 5).isLt

theorem APre.savedMem_big {s₀ : State} (_hp : VG.Proof.CmacAes.Stream.X86.APre s₀) : Frame (VG.Proof.CmacAes.Stream.X86.ABig s₀) s₀.mem (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) :=
  (VG.Proof.CmacAes.Stream.X86.savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.CmacAes.Stream.X86.ascR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Between the calls -/

/-- What holds at every point of the code outside the calls: `esp`, the
regions and the stack arguments are those on entry. -/
structure ACtx (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.CmacAes.Stream.X86.aE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  args : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i

theorem ACtx.of_frame {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (hesp : s.gpr .esp = VG.Proof.CmacAes.Stream.X86.aE s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame (VG.Proof.CmacAes.Stream.X86.ABig s₀) s₀.mem s.mem) : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s :=
  ⟨hesp, hrd, hwr, fun _ hi => hp.keep hf hi⟩

theorem ACtx.upd {s₀ s s' : State} {d : Reg} {v : BitVec 32} (h : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s) (u : Upd s s' d v)
    (hd : d ≠ .esp) : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s' :=
  ⟨by rw [u.other _ (Ne.symm hd), h.esp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.args⟩

theorem ACtx.fupd {s₀ s s' : State} (h : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s) (u : Fupd s s') : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s' :=
  ⟨by rw [u.gpr, h.esp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.args⟩

theorem ACtx.pt {s₀ s : State} (h : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s) : VG.Proof.CmacAes.Stream.X86.Pt 7 s₀ s := ⟨h.esp, h.wr, h.args⟩

/-- `mov d, [esp + 4 + 4 i]`. -/
theorem ACtx.wp_arg {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (h : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s) {d : Reg} (hd : d ≠ .esp) {i : Nat} (hi : i < 7)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (VG.X86.arg s₀ i) → VG.Proof.CmacAes.Stream.X86.ACtx s₀ s' → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (argOp i) :: is)) s Q :=
  VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [h.rd, h.wr]; exact hp.arg_in hi) (h.args i hi)
    fun s' u => k s' u (h.upd u hd)

/-! ## `fill`: how many bytes to copy, and where -/

/-- What `fill` leaves. -/
structure Filled (s₀ s s' : State) : Prop where
  ctx : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s'
  mem : s'.mem = s.mem
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  ebp : s'.gpr .ebp = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  esi : s'.gpr .esi = VG.Proof.CmacAes.Stream.X86.aD s₀
  edi : s'.gpr .edi = VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 (288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀))

theorem fill_wp {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (h : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s)
    (hax : s.gpr .eax = BitVec.ofNat 32 (held (VG.Proof.CmacAes.Stream.X86.aC s₀))) : WP isa fill s (VG.Proof.CmacAes.Stream.X86.Filled s₀ s) := by
  have hh := held_le (VG.Proof.CmacAes.Stream.X86.aC s₀)
  have hL := hp.lt
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.X86.f_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  unfold fill
  refine WP.seq (wp_movi fun s₁ u₁ => wp_sub fun s₂ u₂ _ => (h.upd u₁ (by decide)).upd u₂ (by decide) |>.wp_arg hp
    (by decide) (by decide) fun s₃ u₃ c₃ => wp_cmp fun s₄ f₄ cf₄ _ => WP.block_nil ?_)
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (16 - held (VG.Proof.CmacAes.Stream.X86.aC s₀)) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hax]; exact sub_ofNat hh
  have ecx₄ : s₄.gpr .ecx = BitVec.ofNat 32 (16 - held (VG.Proof.CmacAes.Stream.X86.aC s₀)) := by rw [f₄.gpr, u₃.other _ (by decide), ecx₂]
  have edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.aL s₀) := by rw [f₄.gpr, u₃.gpr]; exact VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 5
  have c₄ := c₃.fupd f₄
  have cf : s₄.cf = some (decide (VG.Proof.CmacAes.Stream.X86.aL s₀ < 16 - held (VG.Proof.CmacAes.Stream.X86.aC s₀))) := by
    rw [cf₄, u₃.gpr, u₃.other _ (by decide), ecx₂, VG.Proof.CmacAes.Stream.X86.toNat_ofNat32 (by omega)]
  have eax₄ : s₄.gpr .eax = s.gpr .eax := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => VG.Proof.CmacAes.Stream.X86.ACtx s₀ s₅ ∧ s₅.mem = s.mem ∧
      s₅.gpr .ecx = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) ∧ s₅.gpr .eax = s.gpr .eax) ?_ fun s₅ h₅ => ?_)
  · have ev : isa.eval .b s₄ = some (decide (VG.Proof.CmacAes.Stream.X86.aL s₀ < 16 - held (VG.Proof.CmacAes.Stream.X86.aC s₀))) := by
      show VG.X86.eval .b s₄ = _; rw [eval_b, cf]
    by_cases hl : VG.Proof.CmacAes.Stream.X86.aL s₀ < 16 - held (VG.Proof.CmacAes.Stream.X86.aC s₀)
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => wp_mov fun s₅ u₅ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₄.upd u₅ (by decide), by rw [u₅.mem, m₄], by rw [u₅.gpr, edx₄, VG.Proof.CmacAes.Stream.X86.fOf, Nat.min_eq_left (by omega)],
        by rw [u₅.other _ (by decide), eax₄]⟩
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => WP.block_nil ?_
      exact ⟨c₄, m₄, by rw [ecx₄, VG.Proof.CmacAes.Stream.X86.fOf, Nat.min_eq_right (by omega)], eax₄⟩
  · obtain ⟨c₅, m₅, ecx₅, eax₅⟩ := h₅
    refine wp_mov fun s₆ u₆ => (c₅.upd u₆ (by decide)).wp_arg hp (by decide) (by decide) fun s₇ u₇ c₇ =>
      c₇.wp_arg hp (by decide) (by decide) fun s₈ u₈ c₈ => wp_addi fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => WP.block_nil ?_
    have fSt : (VG.Proof.CmacAes.Stream.X86.aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
    refine ⟨(c₈.upd u₉ (by decide)).upd u₁₀ (by decide), by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅],
      ?_, ?_, ?_, ?_⟩
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), ecx₅]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.gpr, ecx₅]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
    · rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), eax₅, hax]
      exact Offset.add_add _ 288 _

/-! ## `chain1`: the arguments of the first call -/

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the regions and stack of `s₀`. -/
theorem APre.uargs {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) {Dd : BitVec 32} {n : Nat}
    (heax : s.gpr .eax = VG.Proof.CmacAes.Stream.X86.aSt s₀) (hecx : s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.aR s₀))
    (hedx : s.gpr .edx = VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272) (hebx : s.gpr .ebx = Dd)
    (hesi : s.gpr .esi = BitVec.ofNat 32 n) (hedi : s.gpr .edi = VG.Proof.CmacAes.Stream.X86.aSc s₀) (hesp : s.gpr .esp = VG.Proof.CmacAes.Stream.X86.aE s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 32)
    (hdc : (⟨Dd.setWidth 64, 16 * n⟩ : Region).Disjoint ⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd.setWidth 64, 16 * n⟩ : Region).Disjoint ⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64, 2176⟩)
    (hstk : (below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56).Disjoint ⟨Dd.setWidth 64, 16 * n⟩) (hfD : Dd.toNat + 16 * n ≤ 2 ^ 32)
    (hcov : ∃ r' ∈ s₀.rd ++ s₀.wr, ∃ off, Dd.setWidth 64 = r'.base + BitVec.ofNat 64 off ∧ off + 16 * n ≤ r'.len) :
    VG.Proof.CmacAes.Stream.X86.UArgs s (VG.Proof.CmacAes.Stream.X86.aSt s₀) (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272) Dd (VG.Proof.CmacAes.Stream.X86.aSc s₀) (VG.Proof.CmacAes.Stream.X86.aR s₀) n := by
  have fSt : (VG.Proof.CmacAes.Stream.X86.aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fS : (VG.Proof.CmacAes.Stream.X86.aSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have p272 : (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272).setWidth 64 = (VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272 :=
    VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)
  have c272 : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272).setWidth 64, 16⟩ (VG.Proof.CmacAes.Stream.X86.astR s₀) := by
    rw [p272]; exact Offset.sub_base _ (by decide)
  exact
  { eax := heax, ecx := hecx, edx := hedx, ebx := hebx, esi := hesi, edi := hedi, rounds := hp.rounds, hn := hn
    esp := by rw [hesp]; exact hp.esp56
    wc := by rw [p272]; exact Offset.base_disjoint _ (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := by rw [p272]; exact hdc
    ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    bW := by rw [hesp]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bD := by rw [hesp]; exact hstk
    bC := by rw [hesp]; exact hp.b_st.sub_right c272
    bS := by rw [hesp]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega
    fC := by rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega
    fD := hfD
    fS := by omega
    reads := by
      rw [hrd, hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp [hp.wr], 0, by simp, by simp⟩
      · exact hcov
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp, 272, p272, by simp⟩
      · exact ⟨VG.Proof.CmacAes.Stream.X86.ascR s₀, by simp, 0, by simp, by simp⟩ }

/-- What `chain1` leaves. -/
structure Chained₁ (s₀ s s' : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86.UArgs s' (VG.Proof.CmacAes.Stream.X86.aSt s₀) (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272) (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 288) (VG.Proof.CmacAes.Stream.X86.aSc s₀) (VG.Proof.CmacAes.Stream.X86.aR s₀)
    (VG.Proof.CmacAes.Stream.X86.b1Of (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  ctx : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s'
  ebp : s'.gpr .ebp = s.gpr .ebp
  mem : s'.mem = s.mem

theorem chain1_wp {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (h : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) : WP isa chain1 s (VG.Proof.CmacAes.Stream.X86.Chained₁ s₀ s) := by
  have hL := hp.lt
  have ⟨hfL, _⟩ := VG.Proof.CmacAes.Stream.X86.f_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  have fSt : (VG.Proof.CmacAes.Stream.X86.aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  unfold chain1
  refine WP.seq (wp_movi fun s₁ u₁ => (h.upd u₁ (by decide)).wp_arg hp (by decide) (by decide) fun s₂ u₂ c₂ =>
    wp_sub fun s₃ u₃ z₃ => WP.block_nil ?_)
  have c₃ := c₂.upd u₃ (by decide)
  have z : s₃.zf = some (decide (VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0)) := by
    rw [z₃, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hbp, VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 5, sub_ofNat hfL,
      ofNat_beq_zero (by omega)]; rfl
  have ebp₃ : s₃.gpr .ebp = s.gpr .ebp := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => VG.Proof.CmacAes.Stream.X86.ACtx s₀ s₄ ∧ s₄.mem = s.mem ∧ s₄.gpr .ebp = s.gpr .ebp ∧
      s₄.gpr .esi = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.b1Of (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) ?_ fun s₄ h₄ => ?_)
  · have ev : isa.eval .e s₃ = some (decide (VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0)) := by
      show VG.X86.eval .e s₃ = _; rw [eval_e, z]
    by_cases h0 : VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₃, m₃, ebp₃, by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; simp only [VG.Proof.CmacAes.Stream.X86.b1Of, h0, ↓reduceIte]; rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => wp_movi fun s₄ u₄ => WP.block_nil ?_
      exact ⟨c₃.upd u₄ (by decide), by rw [u₄.mem, m₃], by rw [u₄.other _ (by decide), ebp₃],
        by rw [u₄.gpr]; simp only [VG.Proof.CmacAes.Stream.X86.b1Of, h0, ↓reduceIte]; rfl⟩
  · obtain ⟨c₄, m₄, ebp₄, esi₄⟩ := h₄
    refine c₄.wp_arg hp (by decide) (by decide) fun s₅ u₅ c₅ => c₅.wp_arg hp (by decide) (by decide) fun s₆ u₆ c₆ =>
      wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ =>
      ((((c₆.upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀ (by decide)).wp_arg hp
        (by decide) (by decide) fun s₁₁ u₁₁ c₁₁ => WP.block_nil ?_
    have eax₁₁ : s₁₁.gpr .eax = VG.Proof.CmacAes.Stream.X86.aSt s₀ := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
    have hb1 : 16 * VG.Proof.CmacAes.Stream.X86.b1Of (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) ≤ 16 := by unfold VG.Proof.CmacAes.Stream.X86.b1Of; split <;> omega
    have p288 : (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 288).setWidth 64 = (VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288 :=
      VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)
    have c288 : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 288).setWidth 64, 16 * VG.Proof.CmacAes.Stream.X86.b1Of (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)⟩ (VG.Proof.CmacAes.Stream.X86.astR s₀) := by
      rw [p288]; exact Offset.sub_base _ (by omega)
    refine ⟨hp.uargs eax₁₁ ?_ ?_ ?_ ?_ u₁₁.gpr c₁₁.esp c₁₁.rd c₁₁.wr (by omega) ?_
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide))) (hp.b_st.sub_right c288)
      (by rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega) ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp [hp.wr], 288, p288, by simp; omega⟩,
      c₁₁, ?_, ?_⟩
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.gpr]; exact VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 1
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr,
        u₆.other _ (by decide), u₅.gpr]; rfl
    · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr]; rfl
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), esi₄]
    · rw [p288]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), ebp₄]
    · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]

/-! ## `chain2`: the arguments of the second call -/

/-- The data the second call reads: the data left, or, with none left, the
bytes held back (none of which it reads). -/
def d2Of (s₀ : State) : BitVec 32 :=
  if VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0 then VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 288 else VG.Proof.CmacAes.Stream.X86.aD s₀ + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))

/-- What `chain2` leaves. -/
structure Chained₂ (s₀ s s' : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86.UArgs s' (VG.Proof.CmacAes.Stream.X86.aSt s₀) (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272) (VG.Proof.CmacAes.Stream.X86.d2Of s₀) (VG.Proof.CmacAes.Stream.X86.aSc s₀) (VG.Proof.CmacAes.Stream.X86.aR s₀) (VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  ctx : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s'
  ebp : s'.gpr .ebp = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  mem : s'.mem = s.mem

theorem chain2_wp {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (h : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) : WP isa chain2 s (VG.Proof.CmacAes.Stream.X86.Chained₂ s₀ s) := by
  have hL := hp.lt
  have ⟨hfL, _⟩ := VG.Proof.CmacAes.Stream.X86.f_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  have hsum := VG.Proof.CmacAes.Stream.X86.nb_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  have fSt : (VG.Proof.CmacAes.Stream.X86.aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fD : (VG.Proof.CmacAes.Stream.X86.aD s₀).toNat + VG.Proof.CmacAes.Stream.X86.aL s₀ ≤ 2 ^ 32 := hp.fD
  unfold chain2
  refine WP.seq (wp_movi fun s₁ u₁ => (h.upd u₁ (by decide)).wp_arg hp (by decide) (by decide) fun s₂ u₂ c₂ =>
    wp_addi fun s₃ u₃ => (c₂.upd u₃ (by decide)).wp_arg hp (by decide) (by decide) fun s₄ u₄ c₄ =>
    wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have c₅ := c₄.upd u₅ (by decide)
  have ebp₄ : s₄.gpr .ebp = s.gpr .ebp := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have ebp₅ : s₅.gpr .ebp = s.gpr .ebp := by rw [u₅.other _ (by decide), ebp₄]
  have edx₅ : s₅.gpr .edx = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) := by
    rw [u₅.gpr, u₄.gpr, ebp₄, hbp, VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 5, sub_ofNat hfL]; rfl
  have z : s₅.zf = some (decide (VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0)) := by
    rw [z₅, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbp, VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 5, sub_ofNat hfL, ofNat_beq_zero (by omega)]; rfl
  have ecx₅ : s₅.gpr .ecx = BitVec.ofNat 32 0 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  have ebx₅ : s₅.gpr .ebx = VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 288 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr]; rfl
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₆ : State) => VG.Proof.CmacAes.Stream.X86.ACtx s₀ s₆ ∧ s₆.mem = s.mem ∧ s₆.gpr .ebp = s.gpr .ebp ∧
      s₆.gpr .ecx = BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) ∧ s₆.gpr .ebx = VG.Proof.CmacAes.Stream.X86.d2Of s₀) ?_ fun s₆ h₆ => ?_)
  · have ev : isa.eval .e s₅ = some (decide (VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0)) := by
      show VG.X86.eval .e s₅ = _; rw [eval_e, z]
    by_cases h0 : VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₅, m₅, ebp₅, by rw [ecx₅]; simp only [VG.Proof.CmacAes.Stream.X86.nbOf, h0, ↓reduceIte],
        by rw [ebx₅]; simp only [VG.Proof.CmacAes.Stream.X86.d2Of, h0, ↓reduceIte]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_mov fun s₆ u₆ => wp_subi fun s₇ u₇ _ => wp_mov fun s₈ u₈ => wp_andi fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ _ =>
        (((((c₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
          (by decide)).wp_arg hp (by decide) (by decide) fun s₁₁ u₁₁ c₁₁ => wp_add fun s₁₂ u₁₂ => WP.block_nil ?_
      refine ⟨c₁₁.upd u₁₂ (by decide), ?_, ?_, ?_, ?_⟩
      · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
      · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
          u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), ebp₅]
      · have ecx₇ : s₇.gpr .ecx = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) - 1 := by rw [u₇.gpr, u₆.gpr, edx₅]
        have ecx₉ : s₉.gpr .ecx = s₇.gpr .ecx := by rw [u₉.other _ (by decide), u₈.other _ (by decide)]
        have eax₉ : s₉.gpr .eax = s₇.gpr .ecx &&& 15 := by rw [u₉.gpr, u₈.gpr]
        rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, ecx₉, eax₉, ecx₇]
        simp only [VG.Proof.CmacAes.Stream.X86.nbOf, h0, ↓reduceIte]
        exact VG.Proof.CmacAes.Stream.X86.nb16_bv (by omega) (by unfold VG.Proof.CmacAes.Stream.X86.leftOf; omega)
      · rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
          u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), ebp₅, hbp]
        simp only [VG.Proof.CmacAes.Stream.X86.d2Of, h0, ↓reduceIte]
  · obtain ⟨c₆, m₆, ebp₆, ecx₆, ebx₆⟩ := h₆
    have hn16 : 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) < 2 ^ 32 := by omega
    refine wp_mov fun s₇ u₇ => wp_shr (by decide) fun s₈ u₈ => wp_add fun s₉ u₉ =>
      (((c₆.upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).wp_arg hp (by decide) (by decide)
        fun s₁₀ u₁₀ c₁₀ => c₁₀.wp_arg hp (by decide) (by decide) fun s₁₁ u₁₁ c₁₁ => wp_mov fun s₁₂ u₁₂ =>
        wp_addi fun s₁₃ u₁₃ => ((c₁₁.upd u₁₂ (by decide)).upd u₁₃ (by decide)).wp_arg hp (by decide) (by decide)
        fun s₁₄ u₁₄ c₁₄ => WP.block_nil ?_
    have ebx₁₄ : s₁₄.gpr .ebx = VG.Proof.CmacAes.Stream.X86.d2Of s₀ := by
      rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), ebx₆]
    have hnb : VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0 ∨ 0 < VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) := by
      unfold VG.Proof.CmacAes.Stream.X86.nbOf; split <;> omega
    -- The data the call reads.
    have hn0 : VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0 → VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0 := fun h => by simp [VG.Proof.CmacAes.Stream.X86.nbOf, h]
    have hd2 : ((VG.Proof.CmacAes.Stream.X86.d2Of s₀).setWidth 64 = (VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288 ∧ VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0) ∨
        ((VG.Proof.CmacAes.Stream.X86.d2Of s₀).setWidth 64 = (VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) ∧
          0 < VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) := by
      unfold VG.Proof.CmacAes.Stream.X86.d2Of
      split
      · exact .inl ⟨VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega), hn0 (by assumption)⟩
      · exact .inr ⟨VG.Proof.CmacAes.Stream.X86.add_setWidth (by unfold VG.Proof.CmacAes.Stream.X86.leftOf at *; omega), by omega⟩
    have dD : 0 < VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) →
        Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)), 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)⟩
          (VG.Proof.CmacAes.Stream.X86.adR s₀) := fun _ => Offset.sub_base _ (by omega)
    refine ⟨hp.uargs ?_ ?_ ?_ ebx₁₄ ?_ u₁₄.gpr c₁₄.esp c₁₄.rd c₁₄.wr hn16 ?_ ?_ ?_ ?_ ?_, c₁₄, ?_, ?_⟩
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.gpr]
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr]
      exact VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 1
    · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr]; rfl
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr, ecx₆]
      exact VG.Proof.CmacAes.Stream.X86.shr4 hn16
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (hp.st_d.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (dD hl)
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
      · exact (hp.d_s.sub_left (dD hl)).sub_right (Region.sub_prefix (by decide))
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact hp.b_st.sub_right (Offset.sub_base _ (by omega))
      · exact hp.b_d.sub_right (dD hl)
    · unfold VG.Proof.CmacAes.Stream.X86.d2Of
      split
      · rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega
      · rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by unfold VG.Proof.CmacAes.Stream.X86.leftOf at *; omega)]; omega
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp [hp.wr], 288, rfl, by simp; omega⟩
      · exact ⟨VG.Proof.CmacAes.Stream.X86.adR s₀, by simp [hp.rd], VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀), rfl, by simp; omega⟩
    · have ebp₈ : s₈.gpr .ebp = s.gpr .ebp := by
        rw [u₈.other _ (by decide), u₇.other _ (by decide), ebp₆]
      have ecx₈ : s₈.gpr .ecx = BitVec.ofNat 32 (16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) := by
        rw [u₈.other _ (by decide), u₇.other _ (by decide), ecx₆]
      rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.other _ (by decide), u₉.gpr, ebp₈, ecx₈, hbp]
      exact (BitVec.ofNat_add _ _).symm
    · rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]

/-! ## `rest`: the arguments of the last copy -/

/-- What `rest` leaves. -/
structure Rested (s₀ s s' : State) : Prop where
  ctx : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s'
  mem : s'.mem = s.mem
  esi : s'.gpr .esi = VG.Proof.CmacAes.Stream.X86.aD s₀ + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  edi : s'.gpr .edi = VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 288
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))

theorem rest_wp {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (h : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) :
    WP isa (.block rest) s (VG.Proof.CmacAes.Stream.X86.Rested s₀ s) := by
  have hsum := VG.Proof.CmacAes.Stream.X86.nb_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  have hsum' : VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = (VG.X86.arg s₀ 5).toNat := hsum
  unfold rest
  refine h.wp_arg hp (by decide) (by decide) fun s₁ u₁ c₁ => wp_add fun s₂ u₂ =>
    (c₁.upd u₂ (by decide)).wp_arg hp (by decide) (by decide) fun s₃ u₃ c₃ => wp_addi fun s₄ u₄ =>
    (c₃.upd u₄ (by decide)).wp_arg hp (by decide) (by decide) fun s₅ u₅ c₅ => wp_sub fun s₆ u₆ _ => WP.block_nil ?_
  refine ⟨c₅.upd u₆ (by decide), by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.gpr, u₁.other _ (by decide), hbp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]; rfl
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbp, VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 5, sub_ofNat (by omega)]
    congr 1; unfold VG.Proof.CmacAes.Stream.X86.restOf VG.Proof.CmacAes.Stream.X86.leftOf; omega

end VG.Proof.CmacAes.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb`. -/
section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` around the calls

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`); after each call, what the code that follows needs (`AAft₁`,
`AAft₂`), and what `chain2` leaves for the second call (`AMid₂`).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

open VG.WriteBytes

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.CmacAes.X86 (wp_arg)
open VG.Proof.Cmac.Stream (held held_le)

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) : Mem :=
  VG.WriteBytes.writeBytes (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀)))
    (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)))

theorem m4_frame (s₀ : State) :
    Frame [⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀)), VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)⟩]
      (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) (VG.Proof.CmacAes.Stream.X86.m4 s₀) :=
  VG.WriteBytes.writeBytes_frame _ _ _ (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)

theorem m4_big {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) : Frame (VG.Proof.CmacAes.Stream.X86.ABig s₀) s₀.mem (VG.Proof.CmacAes.Stream.X86.m4 s₀) := by
  have := VG.Proof.CmacAes.Stream.X86.f_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  exact hp.savedMem_big.trans ((VG.Proof.CmacAes.Stream.X86.m4_frame s₀).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp, Offset.sub_base _ (by omega)⟩)

/-- The save. -/
theorem absSave_wp {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) :
    WP isa (.block absSave) s₀ fun s => VG.Proof.CmacAes.Stream.X86.ACtx s₀ s ∧ s.mem = VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀) := by
  have fS : (VG.X86.arg s₀ 6).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  rw [show absSave = .mov .eax (argOp 6) :: (save ++ []) from rfl]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine VG.Proof.CmacAes.Stream.X86.save_wp (Sc := VG.Proof.CmacAes.Stream.X86.aSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.ascR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => WP.block_nil ?_
  have hm₂ : s₂.mem = VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀) := by
    rw [m₂, u₁.mem, VG.Proof.CmacAes.Stream.X86.savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacAes.Stream.X86.saved_ne_eax p hp')
  exact ⟨ACtx.of_frame hp (by rw [g₂, u₁.other _ (by decide)]) (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr])
    (hm₂ ▸ hp.savedMem_big), hm₂⟩

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86.UArgs s (VG.Proof.CmacAes.Stream.X86.aSt s₀) (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272) (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 288) (VG.Proof.CmacAes.Stream.X86.aSc s₀) (VG.Proof.CmacAes.Stream.X86.aR s₀)
    (VG.Proof.CmacAes.Stream.X86.b1Of (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  ctx : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  mem : s.mem = VG.Proof.CmacAes.Stream.X86.m4 s₀

theorem absorbPre_wp {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) : WP isa absorbPre s₀ (VG.Proof.CmacAes.Stream.X86.AMid₁ s₀) := by
  have hL := hp.lt
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.X86.f_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  have fSt : (VG.Proof.CmacAes.Stream.X86.aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fD : (VG.Proof.CmacAes.Stream.X86.aD s₀).toNat + VG.Proof.CmacAes.Stream.X86.aL s₀ ≤ 2 ^ 32 := hp.fD
  unfold absorbPre
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.absSave_wp hp) fun s₁ ⟨c₁, m₁⟩ => ?_)
  refine WP.seq (VG.Proof.CmacAes.Stream.X86.held_ok (r := .eax) (by decide) (by decide) c₁.esp (by rw [c₁.rd, c₁.wr]; exact hp.arg_in (by decide))
    (by rw [c₁.rd, c₁.wr]; exact hp.arg_in (by decide)) (c₁.args 2 (by decide)) (c₁.args 3 (by decide))
    fun s₂ eax₂ g₂ m₂ rd₂ wr₂ => ?_)
  have c₂ : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s₂ := ⟨by rw [g₂ _ (by decide) (by decide), c₁.esp], by rw [rd₂, c₁.rd], by rw [wr₂, c₁.wr],
    by rw [m₂]; exact c₁.args⟩
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.fill_wp hp c₂ eax₂) fun s₃ h₃ => ?_)
  have p288 : 0 < VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) → (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 (288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀))).setWidth 64 =
      (VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀)) := fun _ => VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.copy_wp (L := VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) (by omega) h₃.esi h₃.edi h₃.ecx (fun _ => by omega)
    (fun _ => by rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega)
    (fun _ => by
      rw [h₃.ctx.rd, h₃.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.adR s₀, by simp, 0, by simp, by simp; omega⟩)
    (fun h0 => by
      rw [h₃.ctx.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp, 288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀), p288 h0, by simp; omega⟩)
    (fun h0 => by
      rw [p288 h0]
      exact (hp.st_d.sub_left (Offset.sub_base (d := 288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀)) (n := VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) _
        (by omega))).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  obtain ⟨m₄, g₄, rd₄, wr₄⟩ := h₄
  have hm₄ : s₄.mem = VG.Proof.CmacAes.Stream.X86.m4 s₀ := by
    rw [m₄, h₃.mem, m₂, m₁, VG.Proof.CmacAes.Stream.X86.m4]
    by_cases hf0 : VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0
    · rw [hf0]; simp only [Spec.Aes.bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]
    · rw [p288 (by omega)]
  have c₄ : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s₄ := ACtx.of_frame hp (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ctx.esp])
    (by rw [rd₄, h₃.ctx.rd]) (by rw [wr₄, h₃.ctx.wr]) (hm₄ ▸ VG.Proof.CmacAes.Stream.X86.m4_big hp)
  refine WP.mono (VG.Proof.CmacAes.Stream.X86.chain1_wp hp c₄ (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ebp]))
    fun s₅ h₅ => ⟨h₅.args, h₅.ctx, by rw [h₅.ebp, g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ebp],
      by rw [h₅.mem, hm₄]⟩

/-! ## After the calls -/

/-- What is known after a call. -/
structure AAft (s₀ : State) (v : Nat) (s : State) : Prop where
  ctx : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s
  ebp : s.gpr .ebp = BitVec.ofNat 32 v
  frame : Frame (VG.Proof.CmacAes.Stream.X86.ABig s₀) s₀.mem s.mem

/-- A call of `vg_cmac_aes_update` keeps `AAft`. -/
theorem upd_aft {s₀ s s' : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) {Dd : BitVec 32} {n v : Nat}
    (hf : Frame (VG.Proof.CmacAes.Stream.X86.ABig s₀) s₀.mem s.mem) (hc : VG.Proof.CmacAes.Stream.X86.ACtx s₀ s) (hbp : s.gpr .ebp = BitVec.ofNat 32 v)
    (h : VG.Proof.CmacAes.Stream.X86.UPost s (VG.Proof.CmacAes.Stream.X86.aSt s₀) (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272) Dd (VG.Proof.CmacAes.Stream.X86.aSc s₀) (VG.Proof.CmacAes.Stream.X86.aR s₀) n s') : VG.Proof.CmacAes.Stream.X86.AAft s₀ v s' := by
  have fSt : (VG.Proof.CmacAes.Stream.X86.aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fr := h.frame
  rw [hc.esp, VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)] at fr
  have F : Frame (VG.Proof.CmacAes.Stream.X86.ABig s₀) s₀.mem s'.mem := hf.trans (fr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.Stream.X86.ascR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)
  exact ⟨ACtx.of_frame hp (by rw [h.saved .esp (by simp [calleeSaved]), hc.esp]) (by rw [h.rd, hc.rd])
    (by rw [h.wr, hc.wr]) F, by rw [h.saved .ebp (by simp [calleeSaved]), hbp], F⟩

theorem call1_after {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (h : VG.Proof.CmacAes.Stream.X86.AMid₁ s₀ s) :
    WP isa (call6 ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86.update v.callee)) s (VG.Proof.CmacAes.Stream.X86.AAft s₀ (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) :=
  WP.mono ((VG.Proof.CmacAes.Stream.X86.upd_call v) h.args) fun _ h' => VG.Proof.CmacAes.Stream.X86.upd_aft hp (h.mem ▸ VG.Proof.CmacAes.Stream.X86.m4_big hp) h.ctx h.ebp h'

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86.UArgs s (VG.Proof.CmacAes.Stream.X86.aSt s₀) (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 272) (VG.Proof.CmacAes.Stream.X86.d2Of s₀) (VG.Proof.CmacAes.Stream.X86.aSc s₀) (VG.Proof.CmacAes.Stream.X86.aR s₀) (VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  aft : VG.Proof.CmacAes.Stream.X86.AAft s₀ (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) s

theorem chain2_mid {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (h : VG.Proof.CmacAes.Stream.X86.AAft s₀ (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) s) :
    WP isa chain2 s fun s' => VG.Proof.CmacAes.Stream.X86.AMid₂ s₀ s' ∧ s'.mem = s.mem :=
  WP.mono (VG.Proof.CmacAes.Stream.X86.chain2_wp hp h.ctx h.ebp) fun _ h' => ⟨⟨h'.args, h'.ctx, h'.ebp, h'.mem ▸ h.frame⟩, h'.mem⟩

theorem call2_after {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.APre s₀) (h : VG.Proof.CmacAes.Stream.X86.AMid₂ s₀ s) :
    WP isa (call6 ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86.update v.callee)) s
      (VG.Proof.CmacAes.Stream.X86.AAft s₀ (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) :=
  WP.mono ((VG.Proof.CmacAes.Stream.X86.upd_call v) h.args) fun _ h' => VG.Proof.CmacAes.Stream.X86.upd_aft hp h.aft.frame h.aft.ctx h.aft.ebp h'

end VG.Proof.CmacAes.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.AbsorbCorrect`. -/
section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

open VG.WriteBytes

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Proof.Cmac.Stream (held held_le)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem bytesAt_zero (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 0 = [] := rfl

theorem absorb_wp {s₀ : State} (h0 : absorbX86.pre s₀) :
    WP isa (absorb v.callee v.suffix) s₀ fun s' => abiPreserved s₀ s' ∧ absorbX86.post s₀ s' := by
  have hp := APre.of h0
  have hL := hp.lt
  have fSt : (VG.Proof.CmacAes.Stream.X86.aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fD : (VG.Proof.CmacAes.Stream.X86.aD s₀).toNat + VG.Proof.CmacAes.Stream.X86.aL s₀ ≤ 2 ^ 32 := hp.fD
  have fS : (VG.Proof.CmacAes.Stream.X86.aSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e56 := hp.esp56
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.X86.f_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  have hsum := VG.Proof.CmacAes.Stream.X86.nb_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  have hrr := VG.Proof.CmacAes.Stream.X86.rest_le (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)
  have hh := held_le (VG.Proof.CmacAes.Stream.X86.aC s₀)
  unfold absorb
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.absorbPre_wp hp) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono ((VG.Proof.CmacAes.Stream.X86.upd_call v) h₅.args) fun s₆ h₆ => ?_)
  have a₆ := VG.Proof.CmacAes.Stream.X86.upd_aft hp (h₅.mem ▸ VG.Proof.CmacAes.Stream.X86.m4_big hp) h₅.ctx h₅.ebp h₆
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.chain2_mid hp a₆) fun s₇ ⟨h₇, m₇⟩ => ?_)
  refine WP.seq (WP.mono ((VG.Proof.CmacAes.Stream.X86.upd_call v) h₇.args) fun s₈ h₈ => ?_)
  have a₈ := VG.Proof.CmacAes.Stream.X86.upd_aft hp h₇.aft.frame h₇.aft.ctx h₇.aft.ebp h₈
  unfold absorbPost
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.rest_wp hp a₈.ctx a₈.ebp) fun s₉ h₉ => ?_)
  -- The last copy.
  have hsrc : 0 < VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) →
      (VG.Proof.CmacAes.Stream.X86.aD s₀ + BitVec.ofNat 32 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))).setWidth 64 =
        (VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) :=
    fun _ => VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)
  have p288 : (VG.Proof.CmacAes.Stream.X86.aSt s₀ + BitVec.ofNat 32 288).setWidth 64 = (VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288 :=
    VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.copy_wp (L := VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) (by omega) h₉.esi h₉.edi h₉.ecx
    (fun _ => by rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega) (fun _ => by rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega)
    (fun h => by
      rw [h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.CmacAes.Stream.X86.adR s₀, by simp, _, hsrc h, by simp; omega⟩)
    (fun _ => by
      rw [h₉.ctx.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp, 288, p288, by simp; omega⟩)
    (fun h => by
      rw [hsrc h, p288]
      exact (hp.st_d.sub_left (Offset.sub_base (d := 288) (n := VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) _ (by omega))).symm.sub_left
        (Offset.sub_base (d := VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) (n := VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) _
          (by omega)))) fun s₁₀ h₁₀ => ?_)
  obtain ⟨m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := h₁₀
  -- The frames.
  have f6 : Frame [⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64, 2176⟩,
      below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56] s₅.mem s₆.mem := by
    have := h₆.frame; rw [h₅.ctx.esp, VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)] at this; exact this
  have f8 : Frame [⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64, 2176⟩,
      below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56] s₆.mem s₈.mem := by
    have := h₈.frame; rw [h₇.aft.ctx.esp, VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega), m₇] at this; exact this
  have m₁₀' : s₁₀.mem = VG.WriteBytes.writeBytes s₈.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
      (Spec.Aes.bytesAt s₈.mem ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)))
        (VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) := by
    rw [m₁₀, h₉.mem, p288]
    by_cases hr0 : VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0
    · rw [hr0, VG.Proof.CmacAes.Stream.X86.bytesAt_zero, VG.Proof.CmacAes.Stream.X86.bytesAt_zero]
    · rw [hsrc (by omega)]
  have hlr : (Spec.Aes.bytesAt s₈.mem ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) +
      16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) (VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))).length = VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) :=
    Proof.Cmac.bytesAt_length _ _ _
  have fC2 : Frame [⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288, VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)⟩] s₈.mem s₁₀.mem := by
    rw [m₁₀']; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hlr]; exact Region.contains_self _ _)
  have fSv : Frame [⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩] s₀.mem (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) :=
    VG.Proof.CmacAes.Stream.X86.savedMem_frame _ _
  have fC1 : Frame [⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀)), VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)⟩]
      (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) s₅.mem := by rw [h₅.mem]; exact VG.Proof.CmacAes.Stream.X86.m4_frame s₀
  let K : List Region := [⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩,
    ⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (VG.Proof.CmacAes.Stream.X86.aC s₀)), VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)⟩,
    ⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64, 2176⟩, below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56,
    ⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288, VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fSv.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  have KB : Frame (VG.Proof.CmacAes.Stream.X86.ABig s₀) s₀.mem s₁₀.mem := F10.sub fun r hr => by
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.Stream.X86.ascR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.Stream.X86.ascR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.Stream.X86.astR s₀, by simp, Offset.sub_base _ (by omega)⟩
  -- The saved registers.
  have slots : ∀ r d, (r, d) ∈ saved →
      s₁₀.mem.readW ((VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := VG.Proof.CmacAes.Stream.X86.saved_bound _ hrd
    have Fp : Frame K.tail (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) s₁₀.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have sub : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (VG.Proof.CmacAes.Stream.X86.ascR s₀) := Offset.sub_base _ (by omega)
    rw [Fp.readW (Region.contains_self _ _) (fun q hq => ?_) (by decide)]
    · exact VG.Proof.CmacAes.Stream.X86.saveMem_slot _ _ _ hrd
    simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).symm.sub_left sub
  have esp₁₀ : s₁₀.gpr .esp = VG.Proof.CmacAes.Stream.X86.aE s₀ := by
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), h₉.ctx.esp]
  refine WP.mono (VG.Proof.CmacAes.Stream.X86.restore_wp (s₀ := s₀) (i := 6) (Sc := VG.Proof.CmacAes.Stream.X86.aSc s₀) esp₁₀
    (by rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr]; exact hp.arg_in (by decide)) (hp.keep KB (by decide)) fS (by
      rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.ascR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₁₁ ⟨hcs, m₁₁⟩ => ?_
  have F11 : Frame K s₀.mem s₁₁.mem := m₁₁ ▸ F10
  -- The key, the data and the return address are in none of these.
  have dK : ∀ r ∈ K, (⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
    · exact Offset.base_disjoint _ (by omega) (by omega)
    · exact Offset.base_disjoint _ (by omega) (by omega)
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_st.sub_right (Region.sub_prefix (by decide))).symm
    · exact Offset.base_disjoint _ (by omega) (by omega)
  have dDat : ∀ r ∈ K, (VG.Proof.CmacAes.Stream.X86.adR s₀).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_d.symm
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega))
  have dRet : ∀ r ∈ K, (⟨(VG.Proof.CmacAes.Stream.X86.aE s₀).setWidth 64, 4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact VG.Proof.CmacAes.Stream.X86.ret_below e56
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega))
  refine ⟨⟨hcs, F11.readW (r := ⟨(VG.Proof.CmacAes.Stream.X86.aE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  intro key msg hr hRk hcnt hlen
  show Spec.Cmac.Repr s₁₁.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64) key
    (msg ++ Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.aL s₀))
  have hcm : VG.Proof.CmacAes.Stream.X86.aC s₀ = msg.length := by
    show (VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat = _
    rw [hcnt, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hR : VG.Proof.CmacAes.Stream.X86.aR s₀ = Spec.Aes.rounds (key.length / 4) := hRk
  have hRb : 16 * (VG.Proof.CmacAes.Stream.X86.aR s₀ + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
  have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
  rw [← hR] at hsch
  have ciph : ∀ m : Mem, Frame K s₀.mem m →
      Spec.Cmac.aesWith (VG.Proof.CmacAes.Stream.X86.aR s₀) (Spec.Aes.bytesAt m ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64) (16 * (VG.Proof.CmacAes.Stream.X86.aR s₀ + 1))) =
        Spec.Cmac.aes key := fun m hf => by
    rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
      Spec.Cmac.aes, ← hR]
  -- The data, wherever it is read.
  have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ VG.Proof.CmacAes.Stream.X86.aL s₀ →
      Spec.Aes.bytesAt m ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64 + BitVec.ofNat 64 a) b =
        ((Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.aL s₀)).drop a).take b := fun m hf a b hab => by
    rw [Proof.Cmac.Stream.bytesAt_offset m _ hab, Proof.Cmac.bytesAt_frame hf dDat (by omega)]
  have fS' : Frame K s₀.mem (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) := fSv.mono (by simp [K])
  -- The chaining value.
  have cv5 : Spec.Aes.bytesAt s₅.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 := by
    rw [Proof.Cmac.bytesAt_frame fC1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide),
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)]
  have cv11 : Spec.Aes.bytesAt s₁₁.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 =
      Spec.Aes.bytesAt s₈.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 := by
    rw [m₁₁]
    exact Proof.Cmac.bytesAt_frame fC2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by decide)
  have out6 := h₆.out
  rw [VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega), VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega), ciph _ F5] at out6
  have out8 := h₈.out
  rw [VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega), m₇, ciph _ F6] at out8
  have hk : ∀ i < 272, s₁₁.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 i) =
      s₀.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => VG.Proof.CmacAes.Stream.X86.frame_at F11 dK (by simp only [BitVec.toNat_setWidth]; omega) hi
  have hdl : (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.aL s₀)).length = VG.Proof.CmacAes.Stream.X86.aL s₀ :=
    Proof.Cmac.bytesAt_length _ _ _
  have hlf : (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))).length =
      VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) := Proof.Cmac.bytesAt_length _ _ _
  -- The bytes held back so far, and the first `f` bytes of data after them.
  have hb5 : Spec.Aes.bytesAt s₅.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
      (held (VG.Proof.CmacAes.Stream.X86.aC s₀) + VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288) (held (VG.Proof.CmacAes.Stream.X86.aC s₀)) ++
        (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.aL s₀)).take (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) := by
    have e := VG.Proof.CmacAes.Stream.X86.bytesAt_writeBytes (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288) (held (VG.Proof.CmacAes.Stream.X86.aC s₀))
      (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.aSc s₀)) ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) (by rw [hlf]; omega)
    rw [hlf] at e
    rw [h₅.mem, VG.Proof.CmacAes.Stream.X86.m4, ← Offset.add_add, e,
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide)))
        (by omega)]
    refine congrArg (_ ++ ·) ?_
    have := dat _ fS' 0 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) (by omega)
    rwa [BitVec.add_zero, List.drop_zero] at this
  generalize hd : Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.aL s₀) = d at hdl hb5 dat ⊢
  by_cases hx : VG.Proof.CmacAes.Stream.X86.leftOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0
  · -- Everything fits in the block held back.
    have hfL' : VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = VG.Proof.CmacAes.Stream.X86.aL s₀ := by unfold VG.Proof.CmacAes.Stream.X86.leftOf at hx; omega
    have hb : VG.Proof.CmacAes.Stream.X86.b1Of (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0 := by simp [VG.Proof.CmacAes.Stream.X86.b1Of, hx]
    have hn : VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0 := by simp [VG.Proof.CmacAes.Stream.X86.nbOf, hx]
    have hr0 : VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 0 := VG.Proof.CmacAes.Stream.X86.rest_zero hx
    have m118 : s₁₁.mem = s₈.mem := by
      rw [m₁₁, m₁₀', hr0, VG.Proof.CmacAes.Stream.X86.bytesAt_zero, VG.WriteBytes.writeBytes_nil]
    refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl, ← hcm]; omega) ?_ ?_
    · show Spec.Aes.bytesAt _ ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _ =
        Spec.Aes.bytesAt _ ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _
      rw [cv11, out8, hn, VG.Proof.CmacAes.Stream.X86.blocksAt_zero, out6, hb, VG.Proof.CmacAes.Stream.X86.blocksAt_zero]
      exact cv5
    · show Spec.Aes.bytesAt _ ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ =
        Spec.Aes.bytesAt _ ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ ++ _
      rw [← hcm, hdl]
      have sub : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288, held (VG.Proof.CmacAes.Stream.X86.aC s₀) + VG.Proof.CmacAes.Stream.X86.aL s₀⟩ (VG.Proof.CmacAes.Stream.X86.astR s₀) :=
        Offset.sub_base _ (by omega)
      have dj : ∀ r ∈ [⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(VG.Proof.CmacAes.Stream.X86.aSc s₀).setWidth 64, 2176⟩,
          below (VG.Proof.CmacAes.Stream.X86.aE s₀) 56], (⟨(VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288, held (VG.Proof.CmacAes.Stream.X86.aC s₀) + VG.Proof.CmacAes.Stream.X86.aL s₀⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_st.sub_right sub).symm
      have hb5' := hb5
      rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
      rw [m118, Proof.Cmac.bytesAt_frame f8 dj (by omega), Proof.Cmac.bytesAt_frame f6 dj (by omega), hb5']
  · -- The block held back is complete, and more blocks may follow.
    have hlt : 16 - held (VG.Proof.CmacAes.Stream.X86.aC s₀) < VG.Proof.CmacAes.Stream.X86.aL s₀ := by unfold VG.Proof.CmacAes.Stream.X86.leftOf VG.Proof.CmacAes.Stream.X86.fOf at hx; omega
    have hf' : VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 16 - held (VG.Proof.CmacAes.Stream.X86.aC s₀) := by unfold VG.Proof.CmacAes.Stream.X86.fOf; omega
    have hb : VG.Proof.CmacAes.Stream.X86.b1Of (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = 1 := by simp [VG.Proof.CmacAes.Stream.X86.b1Of, hx]
    have hn : VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) = Proof.Cmac.Stream.nblocks (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) := by
      simp only [VG.Proof.CmacAes.Stream.X86.nbOf, hx, ↓reduceIte]
      unfold VG.Proof.CmacAes.Stream.X86.leftOf Proof.Cmac.Stream.nblocks
      rw [hf']
    have hd2 : (VG.Proof.CmacAes.Stream.X86.d2Of s₀).setWidth 64 = (VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) := by
      simp only [VG.Proof.CmacAes.Stream.X86.d2Of, hx, ↓reduceIte]; exact VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)
    have hb5' := hb5
    rw [hf', Nat.add_sub_cancel' hh] at hb5'
    refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl, ← hcm]; exact hlt) ?_ ?_
    · show Spec.Aes.bytesAt _ ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _ =
        Spec.Cmac.chain _ (Spec.Aes.bytesAt _ ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _)
          ([Spec.Aes.bytesAt _ ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ ++ _] ++ _)
      rw [← hcm, hdl]
      rw [cv11, out8, out6, hb, VG.Proof.CmacAes.Stream.X86.blocksAt_one, cv5, Proof.Cmac.chain_append, hd2, Proof.Cmac.Stream.blocksAt_eq,
        dat _ F6 _ _ (by omega), hb5', hf', hn]
    · show Spec.Aes.bytesAt _ ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ = _
      rw [← hcm, hdl]
      have e := VG.Proof.CmacAes.Stream.X86.bytesAt_writeBytes_self s₈.mem ((VG.Proof.CmacAes.Stream.X86.aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
        (xs := Spec.Aes.bytesAt s₈.mem ((VG.Proof.CmacAes.Stream.X86.aD s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) +
          16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) (VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) (by rw [hlr]; omega)
      rw [hlr] at e
      have hr' : VG.Proof.CmacAes.Stream.X86.aL s₀ - (16 - held (VG.Proof.CmacAes.Stream.X86.aC s₀)) - 16 * Proof.Cmac.Stream.nblocks (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) =
          VG.Proof.CmacAes.Stream.X86.restOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) := by
        rw [← hn, ← hf']; rfl
      rw [hr', m₁₁, m₁₀', e, dat _ F8 _ _ (by omega),
        List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold VG.Proof.CmacAes.Stream.X86.restOf VG.Proof.CmacAes.Stream.X86.leftOf; omega),
        List.drop_drop, ← hn, hf']

end VG.Proof.CmacAes.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.Finish`. -/
section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_finish`

The code saves the registers, copies the chaining value to `out`, computes the
number of bytes held back, and calls `vg_cmac_aes_finalize` with the state as
its key and `out` as its state: its result is the MAC of the message the state
represents (`repr_finish`). The code before the call is constant time by the
taint analysis, and the call by its own proof (`fin_rel`), its arguments
pinned by `HMid`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

open VG.WriteBytes

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)
open VG.Proof.CmacAes.X86 (wp_arg toNat_rounds)
open VG.Proof.Cmac.Stream (held held_le)

section
variable (s₀ : State)

abbrev hSt : BitVec 32 := VG.X86.arg s₀ 0
abbrev hR : Nat := (VG.X86.arg s₀ 1).toNat
abbrev hO : BitVec 32 := VG.X86.arg s₀ 4
abbrev hSc : BitVec 32 := VG.X86.arg s₀ 5
abbrev hE : BitVec 32 := s₀.gpr .esp
abbrev hstR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64, 304⟩
abbrev hoR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.hO s₀).setWidth 64, 16⟩
abbrev hscR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.hSc s₀).setWidth 64, 2304⟩
abbrev haR : Region := ⟨argAddr s₀ 0, 24⟩
/-- The bytes held back. -/
abbrev hH : Nat := held (VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat

/-- Where the function writes: the state, `out`, the scratch buffer and the stack. -/
abbrev HBig : List Region := [VG.Proof.CmacAes.Stream.X86.hstR s₀, VG.Proof.CmacAes.Stream.X86.hoR s₀, VG.Proof.CmacAes.Stream.X86.hscR s₀, below (VG.Proof.CmacAes.Stream.X86.hE s₀) 56]

end

/-- The precondition, by name. -/
structure HPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.Stream.X86.haR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.Stream.X86.hstR s₀, VG.Proof.CmacAes.Stream.X86.hoR s₀, VG.Proof.CmacAes.Stream.X86.hscR s₀]
  st_o : (VG.Proof.CmacAes.Stream.X86.hstR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.hoR s₀)
  st_s : (VG.Proof.CmacAes.Stream.X86.hstR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.hscR s₀)
  o_s : (VG.Proof.CmacAes.Stream.X86.hoR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.hscR s₀)
  a_st : (VG.Proof.CmacAes.Stream.X86.haR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.hstR s₀)
  a_o : (VG.Proof.CmacAes.Stream.X86.haR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.hoR s₀)
  a_s : (VG.Proof.CmacAes.Stream.X86.haR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.hscR s₀)
  ret_st : (⟨(VG.Proof.CmacAes.Stream.X86.hE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.hstR s₀)
  ret_o : (⟨(VG.Proof.CmacAes.Stream.X86.hE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.hoR s₀)
  ret_s : (⟨(VG.Proof.CmacAes.Stream.X86.hE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.hscR s₀)
  b_st' : (⟨(VG.Proof.CmacAes.Stream.X86.hE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.hstR s₀)
  b_o' : (⟨(VG.Proof.CmacAes.Stream.X86.hE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.hoR s₀)
  b_s' : (⟨(VG.Proof.CmacAes.Stream.X86.hE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.hscR s₀)
  fSt : (VG.Proof.CmacAes.Stream.X86.hSt s₀).toNat + 304 ≤ 2 ^ 32
  fO : (VG.Proof.CmacAes.Stream.X86.hO s₀).toNat + 16 ≤ 2 ^ 32
  fS : (VG.Proof.CmacAes.Stream.X86.hSc s₀).toNat + 2304 ≤ 2 ^ 32
  esp56 : 56 ≤ (VG.Proof.CmacAes.Stream.X86.hE s₀).toNat
  espfit : (VG.Proof.CmacAes.Stream.X86.hE s₀).toNat + 28 ≤ 2 ^ 32
  rounds : VG.Proof.CmacAes.Stream.X86.hR s₀ = 10 ∨ VG.Proof.CmacAes.Stream.X86.hR s₀ = 12 ∨ VG.Proof.CmacAes.Stream.X86.hR s₀ = 14

theorem HPre.of {s₀ : State} (h : finishX86.pre s₀) : VG.Proof.CmacAes.Stream.X86.HPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩

namespace HPre
variable {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.HPre s₀)
include hp

theorem b_st : (below (VG.Proof.CmacAes.Stream.X86.hE s₀) 56).Disjoint (VG.Proof.CmacAes.Stream.X86.hstR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp56]; exact hp.b_st'
theorem b_o : (below (VG.Proof.CmacAes.Stream.X86.hE s₀) 56).Disjoint (VG.Proof.CmacAes.Stream.X86.hoR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp56]; exact hp.b_o'
theorem b_s : (below (VG.Proof.CmacAes.Stream.X86.hE s₀) 56).Disjoint (VG.Proof.CmacAes.Stream.X86.hscR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp56]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 6 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.CmacAes.Stream.X86.haR s₀, by simp [hp.rd], VG.Proof.CmacAes.Stream.X86.arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `HBig` changes. -/
theorem keep {m : Mem} (hf : Frame (VG.Proof.CmacAes.Stream.X86.HBig s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  VG.Proof.CmacAes.Stream.X86.arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.a_st.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact hp.a_o.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact (VG.Proof.CmacAes.Stream.X86.args_below hp.fit (by decide) hp.esp56).symm.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)

theorem argsOut : ArgsOut 6 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega) hp.ret_o hp.a_o
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega) hp.ret_s hp.a_s

end HPre

theorem HPre.savedMem_big {s₀ : State} (_hp : VG.Proof.CmacAes.Stream.X86.HPre s₀) : Frame (VG.Proof.CmacAes.Stream.X86.HBig s₀) s₀.mem (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.hSc s₀)) :=
  (VG.Proof.CmacAes.Stream.X86.savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.CmacAes.Stream.X86.hscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before the call -/

theorem finSave_eq : finSave = .mov .eax (argOp 5) :: (save ++ ([.mov .esi (argOp 0), .alu .add .esi (.imm 272),
    .mov .edi (argOp 4), .mov .ecx (.imm 16)] : List Instr)) := rfl

/-- What `finSave` leaves. -/
structure HS₁ (s₀ s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.CmacAes.Stream.X86.hSt s₀ + BitVec.ofNat 32 272
  edi : s.gpr .edi = VG.Proof.CmacAes.Stream.X86.hO s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 16
  esp : s.gpr .esp = VG.Proof.CmacAes.Stream.X86.hE s₀
  mem : s.mem = VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.hSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.HPre s₀) : WP isa (.block finSave) s₀ (VG.Proof.CmacAes.Stream.X86.HS₁ s₀) := by
  have fS : (VG.X86.arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  rw [VG.Proof.CmacAes.Stream.X86.finSave_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine VG.Proof.CmacAes.Stream.X86.save_wp (Sc := VG.Proof.CmacAes.Stream.X86.hSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.hscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  have hm₂ : s₂.mem = VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.hSc s₀) := by
    rw [m₂, u₁.mem, VG.Proof.CmacAes.Stream.X86.savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacAes.Stream.X86.saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = VG.Proof.CmacAes.Stream.X86.hE s₀ := by rw [g₂, u₁.other _ (by decide)]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  have av : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 0 (by decide))
    fun s₃ u₃ => wp_addi fun s₄ u₄ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 4 (by decide)) fun s₅ u₅ => wp_movi fun s₆ u₆ => WP.block_nil ?_
  exact ⟨by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]; rfl,
    by rw [u₆.other _ (by decide), u₅.gpr], u₆.gpr,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂],
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂'],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']⟩

/-- The memory after the saves and the copy of the chaining value. -/
def hMem (s₀ : State) : Mem :=
  VG.WriteBytes.writeBytes (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.hSc s₀)) ((VG.Proof.CmacAes.Stream.X86.hO s₀).setWidth 64)
    (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.hSc s₀)) ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16)

theorem hMem_frame {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.HPre s₀) : Frame (VG.Proof.CmacAes.Stream.X86.HBig s₀) s₀.mem (VG.Proof.CmacAes.Stream.X86.hMem s₀) :=
  hp.savedMem_big.trans ((VG.WriteBytes.writeBytes_frame _ _ _ (by
    rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.hoR s₀, by simp, fun _ h => h⟩)

/-- What the code before the call leaves. -/
structure HMid (s₀ s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86.FArgs s (VG.Proof.CmacAes.Stream.X86.hSt s₀) (VG.Proof.CmacAes.Stream.X86.hO s₀) (VG.Proof.CmacAes.Stream.X86.hSt s₀ + BitVec.ofNat 32 288) (VG.Proof.CmacAes.Stream.X86.hSc s₀) (VG.Proof.CmacAes.Stream.X86.hH s₀) (VG.Proof.CmacAes.Stream.X86.hR s₀)
  esp : s.gpr .esp = VG.Proof.CmacAes.Stream.X86.hE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.Proof.CmacAes.Stream.X86.hMem s₀

theorem finPre_wp {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.HPre s₀) : WP isa finPre s₀ (VG.Proof.CmacAes.Stream.X86.HMid s₀) := by
  have fS : (VG.X86.arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (VG.X86.arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO : (VG.X86.arg s₀ 4).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have fSt₂ : (VG.Proof.CmacAes.Stream.X86.hSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO₂ : (VG.Proof.CmacAes.Stream.X86.hO s₀).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have hh₂ : VG.Proof.CmacAes.Stream.X86.hH s₀ ≤ 16 := held_le _
  have fS₂ : (VG.Proof.CmacAes.Stream.X86.hSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e56 := hp.esp56
  unfold finPre
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.finSave_wp hp) fun s₁ h₁ => ?_)
  have p272 : ((VG.Proof.CmacAes.Stream.X86.hSt s₀ + BitVec.ofNat 32 272).setWidth 64) = (VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + BitVec.ofNat 64 272 :=
    VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)
  have c272 : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.hSt s₀ + BitVec.ofNat 32 272).setWidth 64, 16⟩ (VG.Proof.CmacAes.Stream.X86.hstR s₀) := by
    rw [p272]; exact Offset.sub_base _ (by decide)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.copy_wp (L := 16) (by decide) h₁.esi h₁.edi h₁.ecx
    (fun _ => by rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega) (fun _ => by omega)
    (fun _ => by
      rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.CmacAes.Stream.X86.hstR s₀, by simp, 272, p272, by simp⟩)
    (fun _ => by
      rw [h₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.hoR s₀, by simp, 0, by simp, by simp⟩)
    (fun _ => hp.st_o.sub_left c272)) fun s₂ h₂ => ?_)
  obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
  have hm₂ : s₂.mem = VG.Proof.CmacAes.Stream.X86.hMem s₀ := by rw [m₂, h₁.mem, p272]; rfl
  have esp₂ : s₂.gpr .esp = VG.Proof.CmacAes.Stream.X86.hE s₀ := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h₁.esp]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, h₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, h₁.wr]
  have av : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep (VG.Proof.CmacAes.Stream.X86.hMem_frame hp) hi
  refine WP.seq (VG.Proof.CmacAes.Stream.X86.held_ok (r := .esi) (by decide) (by decide) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 2 (by decide)) (av 3 (by decide))
    fun s₃ esi₃ g₃ m₃ rd₃ wr₃ => ?_)
  have esp₃ : s₃.gpr .esp = VG.Proof.CmacAes.Stream.X86.hE s₀ := by rw [g₃ _ (by decide) (by decide), esp₂]
  have rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [rd₃, wr₃, rd₂', wr₂']
  have av₃ : ∀ i < 6, s₃.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => by rw [m₃]; exact av i hi
  unfold finArgs
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₃ (by rw [rw₃]; exact hp.arg_in (by decide)) (av₃ 0 (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), esp₃])
    (by rw [u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide)) (by rw [u₄.mem]; exact av₃ 1 (by decide))
    fun s₅ u₅ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem]; exact av₃ 4 (by decide)) fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), esp₃])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]; exact av₃ 5 (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have esp₉ : s₉.gpr .esp = VG.Proof.CmacAes.Stream.X86.hE s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), esp₃]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂']
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂']
  have m₉ : s₉.mem = VG.Proof.CmacAes.Stream.X86.hMem s₀ := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, hm₂]
  have hh := held_le (VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat
  have p288 : ((VG.Proof.CmacAes.Stream.X86.hSt s₀ + BitVec.ofNat 32 288).setWidth 64) = (VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + BitVec.ofNat 64 288 :=
    VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)
  have cP : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.hSt s₀ + BitVec.ofNat 32 288).setWidth 64, VG.Proof.CmacAes.Stream.X86.hH s₀⟩ (VG.Proof.CmacAes.Stream.X86.hstR s₀) := by
    rw [p288]; exact Offset.sub_base _ (by omega)
  refine ⟨?_, esp₉, rd₉, wr₉, m₉⟩
  exact
  { eax := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.gpr]
    ecx := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr]; exact VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 1
    edx := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
    ebx := by
      rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
    esi := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), esi₃]
    edi := u₉.gpr
    rounds := hp.rounds
    len := hh
    esp := by rw [esp₉]; exact e56
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left cP
    ps := (hp.st_s.sub_left cP).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₉]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bP := by rw [esp₉]; exact hp.b_st.sub_right cP
    bSt := by rw [esp₉]; exact hp.b_o
    bS := by rw [esp₉]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fK := by omega
    fSt := fO
    fP := by rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega
    fS := by omega
    reads := by
      rw [rd₉, wr₉, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.CmacAes.Stream.X86.hstR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.CmacAes.Stream.X86.hstR s₀, by simp, 288, p288, by simp; omega⟩
    writes := by
      rw [wr₉, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.CmacAes.Stream.X86.hoR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.CmacAes.Stream.X86.hscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishX86.pre s₀) :
    WP isa (finish v.callee v.suffix) s₀ fun s' => abiPreserved s₀ s' ∧ finishX86.post s₀ s' := by
  have hp := HPre.of h0
  have fS : (VG.X86.arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (VG.X86.arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO : (VG.X86.arg s₀ 4).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have fSt₂ : (VG.Proof.CmacAes.Stream.X86.hSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO₂ : (VG.Proof.CmacAes.Stream.X86.hO s₀).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have hh₂ : VG.Proof.CmacAes.Stream.X86.hH s₀ ≤ 16 := held_le _
  have fS₂ : (VG.Proof.CmacAes.Stream.X86.hSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e56 := hp.esp56
  unfold finish
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono ((VG.Proof.CmacAes.Stream.X86.fin_call v) h₁.args) fun s₂ h₂ => ?_)
  have f₂ : Frame [VG.Proof.CmacAes.Stream.X86.hoR s₀, ⟨(VG.Proof.CmacAes.Stream.X86.hSc s₀).setWidth 64, 2176⟩, below (VG.Proof.CmacAes.Stream.X86.hE s₀) 56] s₁.mem s₂.mem := by
    have := h₂.frame; rw [h₁.esp] at this; exact this
  have F₂ : Frame (VG.Proof.CmacAes.Stream.X86.HBig s₀) s₀.mem s₂.mem := (h₁.mem ▸ VG.Proof.CmacAes.Stream.X86.hMem_frame hp).trans (f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.Stream.X86.hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.Stream.X86.hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)
  -- The saved registers.
  have slots : ∀ r d, (r, d) ∈ saved →
      s₂.mem.readW ((VG.Proof.CmacAes.Stream.X86.hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := VG.Proof.CmacAes.Stream.X86.saved_bound _ hrd
    have sub : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.hSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (VG.Proof.CmacAes.Stream.X86.hscR s₀) := Offset.sub_base _ (by omega)
    have c := Region.contains_self ((VG.Proof.CmacAes.Stream.X86.hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₂.readW c (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact hp.o_s.symm.sub_left sub
        · exact Offset.disjoint_base _ (by omega) (by omega)
        · exact hp.b_s.symm.sub_left sub) (by decide),
      h₁.mem, VG.Proof.CmacAes.Stream.X86.hMem, (VG.WriteBytes.writeBytes_frame _ _ _ (R := VG.Proof.CmacAes.Stream.X86.hoR s₀) (by
        rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).readW c (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact hp.o_s.symm.sub_left sub) (by decide)]
    exact VG.Proof.CmacAes.Stream.X86.saveMem_slot _ _ _ hrd
  refine WP.mono (VG.Proof.CmacAes.Stream.X86.restore_wp (s₀ := s₀) (i := 5) (Sc := VG.Proof.CmacAes.Stream.X86.hSc s₀) (by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp])
    (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hp.arg_in (by decide)) (hp.keep F₂ (by decide)) fS (by
      rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.hscR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₃ ⟨hcs, m₃⟩ => ?_
  refine ⟨⟨hcs, ?_⟩, ?_⟩
  · rw [m₃]
    refine F₂.readW (r := ⟨(VG.Proof.CmacAes.Stream.X86.hE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_o
    · exact hp.ret_s
    · exact VG.Proof.CmacAes.Stream.X86.ret_below e56
  · intro key msg hr hRk hc hlen
    show Spec.Aes.bytesAt s₃.mem ((VG.Proof.CmacAes.Stream.X86.hO s₀).setWidth 64) 16 = _
    rw [m₃]
    have hn : (VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat = msg.length := by
      rw [hc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen
    -- The state, unchanged before the call.
    have F₁ : Frame [⟨(VG.Proof.CmacAes.Stream.X86.hSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩, VG.Proof.CmacAes.Stream.X86.hoR s₀] s₀.mem s₁.mem := by
      rw [h₁.mem, VG.Proof.CmacAes.Stream.X86.hMem]
      exact ((VG.Proof.CmacAes.Stream.X86.savedMem_frame _ _).mono (by simp)).trans ((VG.WriteBytes.writeBytes_frame _ _ _ (R := VG.Proof.CmacAes.Stream.X86.hoR s₀) (by
        rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).mono (by simp))
    have fSt' : ∀ {d n : Nat}, d + n ≤ 304 →
        Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + BitVec.ofNat 64 d) n =
          Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + BitVec.ofNat 64 d) n := fun {d n} hd => by
      refine Proof.Cmac.bytesAt_frame F₁ (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ (by decide))
      · exact hp.st_o.sub_left (Offset.sub_base _ hd)
    have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := (Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr
    have hR' : VG.Proof.CmacAes.Stream.X86.hR s₀ = Spec.Aes.rounds (key.length / 4) := hRk
    have hRb : 16 * (VG.Proof.CmacAes.Stream.X86.hR s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
    have hsch : Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64) (16 * (VG.Proof.CmacAes.Stream.X86.hR s₀ + 1)) = Spec.Aes.expandKey key := by
      have := fSt' (d := 0) (n := 16 * (VG.Proof.CmacAes.Stream.X86.hR s₀ + 1)) (by omega)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith (VG.Proof.CmacAes.Stream.X86.hR s₀) (Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64) (16 * (VG.Proof.CmacAes.Stream.X86.hR s₀ + 1))) =
        Spec.Cmac.aes key := by rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + 240) 32 =
        Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + 240) 32 := fSt' (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.Stream.X86.hO s₀).setWidth 64) 16 =
        Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + 272) 16 := by
      rw [h₁.mem, VG.Proof.CmacAes.Stream.X86.hMem]
      have := VG.Proof.CmacAes.Stream.X86.bytesAt_writeBytes_self (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.hSc s₀)) ((VG.Proof.CmacAes.Stream.X86.hO s₀).setWidth 64)
        (xs := Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.hSc s₀)) ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16)
        (by rw [Proof.Cmac.bytesAt_length]; decide)
      rw [Proof.Cmac.bytesAt_length] at this
      rw [this]
      exact Proof.Cmac.bytesAt_frame (VG.Proof.CmacAes.Stream.X86.savedMem_frame _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)
    have e₃ : Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀ + BitVec.ofNat 32 288).setWidth 64) (VG.Proof.CmacAes.Stream.X86.hH s₀) =
        Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.hSt s₀).setWidth 64 + 288) (held msg.length) := by
      rw [VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega), ← hn]; exact fSt' (by have := held_le (VG.Proof.CmacAes.Stream.X86.countX86 s₀).toNat; omega)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish hr
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [VG.Proof.CmacAes.Stream.X86.hH, hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

/-- What the call leaves. -/
structure HAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.CmacAes.Stream.X86.hE s₀
  wr : s.wr = s₀.wr
  frame : Frame (VG.Proof.CmacAes.Stream.X86.HBig s₀) s₀.mem s.mem

theorem fin_after {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.HPre s₀) (h : VG.Proof.CmacAes.Stream.X86.HMid s₀ s) :
    WP isa (call6 ("vg_cmac_aes_finalize" ++ v.suffix) (Impl.CmacAes.X86.finalize v.callee)) s (VG.Proof.CmacAes.Stream.X86.HAft s₀) :=
  WP.mono ((VG.Proof.CmacAes.Stream.X86.fin_call v) h.args) fun s' h' => by
    have fr := h'.frame
    rw [h.esp] at fr
    refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.wr, h.wr],
      (h.mem ▸ VG.Proof.CmacAes.Stream.X86.hMem_frame hp).trans (fr.sub fun r hr => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.Stream.X86.hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.Stream.X86.hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem finish_rel {s₀ s₀' : State} (h0 : finishX86.pre s₀) (h0' : finishX86.pre s₀')
    (hq : finishX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish v.callee v.suffix) fun _ _ => True := by
  have hp := HPre.of h0
  have hp' := HPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : VG.Proof.CmacAes.Stream.X86.hSt s₀ = VG.Proof.CmacAes.Stream.X86.hSt s₀' := qa 0 (by decide)
  have e1 : VG.Proof.CmacAes.Stream.X86.hR s₀ = VG.Proof.CmacAes.Stream.X86.hR s₀' := by rw [VG.Proof.CmacAes.Stream.X86.hR, VG.Proof.CmacAes.Stream.X86.hR, qa 1 (by decide)]
  have eH : VG.Proof.CmacAes.Stream.X86.hH s₀ = VG.Proof.CmacAes.Stream.X86.hH s₀' := by rw [VG.Proof.CmacAes.Stream.X86.hH, VG.Proof.CmacAes.Stream.X86.hH, VG.Proof.CmacAes.Stream.X86.countX86, VG.Proof.CmacAes.Stream.X86.countX86, qa 2 (by decide), qa 3 (by decide)]
  have e4 : VG.Proof.CmacAes.Stream.X86.hO s₀ = VG.Proof.CmacAes.Stream.X86.hO s₀' := qa 4 (by decide)
  have e5 : VG.Proof.CmacAes.Stream.X86.hSc s₀ = VG.Proof.CmacAes.Stream.X86.hSc s₀' := qa 5 (by decide)
  have ag : ∀ {a b : State}, VG.Proof.CmacAes.Stream.X86.Pt 6 s₀ a → VG.Proof.CmacAes.Stream.X86.Pt 6 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 6)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := finPre) (by taint_decide)).wp (F₁ := VG.Proof.CmacAes.Stream.X86.HMid s₀) (F₂ := VG.Proof.CmacAes.Stream.X86.HMid s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.X86.finPre_wp hp, VG.Proof.CmacAes.Stream.X86.finPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c := ((VG.Proof.CmacAes.Stream.X86.fin_rel v (E := VG.Proof.CmacAes.Stream.X86.hE s₀) (Q := fun a b => VG.Proof.CmacAes.Stream.X86.HMid s₀ a ∧ VG.Proof.CmacAes.Stream.X86.HMid s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, eH, e4, e5]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := VG.Proof.CmacAes.Stream.X86.HAft s₀) (F₂ := VG.Proof.CmacAes.Stream.X86.HAft s₀') fun _ _ h => ⟨(VG.Proof.CmacAes.Stream.X86.fin_after v) hp h.1, (VG.Proof.CmacAes.Stream.X86.fin_after v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.X86.HAft s₀ a ∧ VG.Proof.CmacAes.Stream.X86.HAft s₀' b) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => ag ⟨h.1.esp, h.1.wr, fun _ hi => hp.keep h.1.frame hi⟩
      ⟨h.2.esp, h.2.wr, fun _ hi => hp'.keep h.2.frame hi⟩) (c := .block (restore 5)) (by taint_decide)
  exact a.seq (c.seq b)

theorem finish_ct : ConstantTime isa finishX86.pre finishX86.pub (finish v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((VG.Proof.CmacAes.Stream.X86.finish_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.Init`. -/
section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_init`

The code saves the registers in the scratch buffer, expands the key into the
state, derives the subkeys after the schedule, zeroes the chaining value and
restores the registers: the state then represents the empty message. The code
between the calls is constant time by the taint analysis (from `esp` and the
stack arguments), and the calls by their own proofs (`ek_rel`, `sub_rel`),
their arguments pinned by `IMid₁` and `IMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_addi wp_shr)
open VG.Proof.CmacAes.X86 (wp_arg zero4_ok)

section
variable (s₀ : State)

abbrev iSt : BitVec 32 := VG.X86.arg s₀ 0
abbrev iKp : BitVec 32 := VG.X86.arg s₀ 1
abbrev iKL : Nat := (VG.X86.arg s₀ 2).toNat
abbrev iSc : BitVec 32 := VG.X86.arg s₀ 3
abbrev iE : BitVec 32 := s₀.gpr .esp
abbrev istR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64, 304⟩
abbrev ikR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.iKp s₀).setWidth 64, VG.Proof.CmacAes.Stream.X86.iKL s₀⟩
abbrev iscR : Region := ⟨(VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64, 2304⟩
abbrev iaR : Region := ⟨argAddr s₀ 0, 16⟩

/-- Where the function writes: the state, the scratch buffer and the stack. -/
abbrev IBig : List Region := [VG.Proof.CmacAes.Stream.X86.istR s₀, VG.Proof.CmacAes.Stream.X86.iscR s₀, below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.Stream.X86.ikR s₀, VG.Proof.CmacAes.Stream.X86.iaR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.Stream.X86.istR s₀, VG.Proof.CmacAes.Stream.X86.iscR s₀]
  st_k : (VG.Proof.CmacAes.Stream.X86.istR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.ikR s₀)
  st_s : (VG.Proof.CmacAes.Stream.X86.istR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.iscR s₀)
  k_s : (VG.Proof.CmacAes.Stream.X86.ikR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.iscR s₀)
  a_st : (VG.Proof.CmacAes.Stream.X86.iaR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.istR s₀)
  a_s : (VG.Proof.CmacAes.Stream.X86.iaR s₀).Disjoint (VG.Proof.CmacAes.Stream.X86.iscR s₀)
  ret_st : (⟨(VG.Proof.CmacAes.Stream.X86.iE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.istR s₀)
  ret_s : (⟨(VG.Proof.CmacAes.Stream.X86.iE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.iscR s₀)
  b_st' : (⟨(VG.Proof.CmacAes.Stream.X86.iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.istR s₀)
  b_k' : (⟨(VG.Proof.CmacAes.Stream.X86.iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.ikR s₀)
  b_s' : (⟨(VG.Proof.CmacAes.Stream.X86.iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (VG.Proof.CmacAes.Stream.X86.iscR s₀)
  fSt : (VG.Proof.CmacAes.Stream.X86.iSt s₀).toNat + 304 ≤ 2 ^ 32
  fK : (VG.Proof.CmacAes.Stream.X86.iKp s₀).toNat + VG.Proof.CmacAes.Stream.X86.iKL s₀ ≤ 2 ^ 32
  fS : (VG.Proof.CmacAes.Stream.X86.iSc s₀).toNat + 2304 ≤ 2 ^ 32
  esp48 : 48 ≤ (VG.Proof.CmacAes.Stream.X86.iE s₀).toNat
  espfit : (VG.Proof.CmacAes.Stream.X86.iE s₀).toNat + 20 ≤ 2 ^ 32
  klen : VG.Proof.CmacAes.Stream.X86.iKL s₀ = 16 ∨ VG.Proof.CmacAes.Stream.X86.iKL s₀ = 24 ∨ VG.Proof.CmacAes.Stream.X86.iKL s₀ = 32

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : VG.Proof.CmacAes.Stream.X86.IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

namespace IPre
variable {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀)
include hp

theorem b_st : (below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48).Disjoint (VG.Proof.CmacAes.Stream.X86.istR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp48]; exact hp.b_st'
theorem b_k : (below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48).Disjoint (VG.Proof.CmacAes.Stream.X86.ikR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp48]; exact hp.b_k'
theorem b_s : (below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48).Disjoint (VG.Proof.CmacAes.Stream.X86.iscR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp48]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.CmacAes.Stream.X86.iaR s₀, by simp [hp.rd], VG.Proof.CmacAes.Stream.X86.arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `IBig` changes. -/
theorem keep {m : Mem} (hf : Frame (VG.Proof.CmacAes.Stream.X86.IBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  VG.Proof.CmacAes.Stream.X86.arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_st.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact (VG.Proof.CmacAes.Stream.X86.args_below hp.fit (by decide) hp.esp48).symm.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)

theorem argsOut : ArgsOut 4 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_s hp.a_s

end IPre

theorem IPre.savedMem_big {s₀ : State} (_hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) : Frame (VG.Proof.CmacAes.Stream.X86.IBig s₀) s₀.mem (VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.iSc s₀)) :=
  (VG.Proof.CmacAes.Stream.X86.savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.CmacAes.Stream.X86.iscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before the first call -/

theorem initPre_eq : initPre = .mov .eax (argOp 3) :: (save ++ ([.mov .eax (argOp 1), .mov .ecx (argOp 2),
    .mov .edx (argOp 0), .mov .ebx (argOp 3)] : List Instr)) := rfl

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86.EArgs s (VG.Proof.CmacAes.Stream.X86.iKp s₀) (VG.Proof.CmacAes.Stream.X86.iSt s₀) (VG.Proof.CmacAes.Stream.X86.iSc s₀) (VG.Proof.CmacAes.Stream.X86.iKL s₀)
  esp : s.gpr .esp = VG.Proof.CmacAes.Stream.X86.iE s₀
  mem : s.mem = VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.iSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) : WP isa (.block initPre) s₀ (VG.Proof.CmacAes.Stream.X86.IMid₁ s₀) := by
  have fS := hp.fS
  have fSt := hp.fSt
  have e48 := hp.esp48
  rw [VG.Proof.CmacAes.Stream.X86.initPre_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine VG.Proof.CmacAes.Stream.X86.save_wp (Sc := VG.Proof.CmacAes.Stream.X86.iSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.iscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  have hm₂ : s₂.mem = VG.Proof.CmacAes.Stream.X86.savedMem s₀ (VG.Proof.CmacAes.Stream.X86.iSc s₀) := by
    rw [m₂, u₁.mem, VG.Proof.CmacAes.Stream.X86.savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacAes.Stream.X86.saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = VG.Proof.CmacAes.Stream.X86.iE s₀ := by rw [g₂, u₁.other _ (by decide)]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  have av : ∀ i < 4, s₂.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 1 (by decide))
    fun s₃ u₃ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide)) (by rw [u₃.mem]; exact av 2 (by decide))
    fun s₄ u₄ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 0 (by decide)) fun s₅ u₅ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have esp₆ : s₆.gpr .esp = VG.Proof.CmacAes.Stream.X86.iE s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂']
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']
  have b20 : Region.Sub (below (VG.Proof.CmacAes.Stream.X86.iE s₀) 20) (below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48) := below_sub (by decide) e48
  refine ⟨?_, esp₆, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], rd₆, wr₆⟩
  exact
  { eax := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    ecx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; exact VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 2
    edx := by rw [u₆.other _ (by decide), u₅.gpr]
    ebx := u₆.gpr
    klen := hp.klen
    esp := by rw [esp₆]; omega
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₆]; exact hp.b_k.sub_left b20
    bW := by rw [esp₆]; exact (hp.b_st.sub_left b20).sub_right (Region.sub_prefix (by decide))
    bS := by rw [esp₆]; exact (hp.b_s.sub_left b20).sub_right (Region.sub_prefix (by decide))
    fK := hp.fK
    fW := by omega
    fS := by omega
    reads := by
      rw [rd₆, wr₆, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.ikR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₆, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.CmacAes.Stream.X86.istR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.CmacAes.Stream.X86.iscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## After a call -/

/-- What is known after each call. -/
structure IAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.CmacAes.Stream.X86.iE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (VG.Proof.CmacAes.Stream.X86.IBig s₀) s₀.mem s.mem

theorem IAft.pt {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) (h : VG.Proof.CmacAes.Stream.X86.IAft s₀ s) : VG.Proof.CmacAes.Stream.X86.Pt 4 s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.keep h.frame hi⟩

theorem IMid₁.after {s₀ s s' : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) (h : VG.Proof.CmacAes.Stream.X86.IMid₁ s₀ s)
    (h' : VG.Proof.CmacAes.Stream.X86.EPost s (VG.Proof.CmacAes.Stream.X86.iKp s₀) (VG.Proof.CmacAes.Stream.X86.iSt s₀) (VG.Proof.CmacAes.Stream.X86.iSc s₀) (VG.Proof.CmacAes.Stream.X86.iKL s₀) s') : VG.Proof.CmacAes.Stream.X86.IAft s₀ s' := by
  have fr := h'.frame
  rw [h.esp, h.mem] at fr
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    hp.savedMem_big.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨VG.Proof.CmacAes.Stream.X86.istR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨VG.Proof.CmacAes.Stream.X86.iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48, by simp, below_sub (by decide) hp.esp48⟩

theorem ek_after {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) (h : VG.Proof.CmacAes.Stream.X86.IMid₁ s₀ s) :
    WP isa (call4 v.expand.name v.expand.code) s (VG.Proof.CmacAes.Stream.X86.IAft s₀) :=
  WP.mono ((VG.Proof.CmacAes.Stream.X86.ek_call v) h.args) fun _ h' => h.after hp h'

/-! ## Between the calls -/

theorem rounds32 {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 32 KL >>> 2 + 6 = BitVec.ofNat 32 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86.SArgs s (VG.Proof.CmacAes.Stream.X86.iSt s₀) (VG.Proof.CmacAes.Stream.X86.iSt s₀ + BitVec.ofNat 32 240) (VG.Proof.CmacAes.Stream.X86.iSc s₀) (VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4 + 6)
  aft : VG.Proof.CmacAes.Stream.X86.IAft s₀ s

theorem initMid_wp {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) (h : VG.Proof.CmacAes.Stream.X86.IAft s₀ s) :
    WP isa (.block initMid) s fun s' => VG.Proof.CmacAes.Stream.X86.IMid₂ s₀ s' ∧ s'.mem = s.mem := by
  have fS := hp.fS
  have fSt := hp.fSt
  have e48 := hp.esp48
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have av : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => hp.keep h.frame hi
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (av 0 (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact av 2 (by decide))
    fun s₂ u₂ => ?_
  refine wp_shr (by decide) fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have esp₇ : s₇.gpr .esp = VG.Proof.CmacAes.Stream.X86.iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have kSt : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀ + BitVec.ofNat 32 240).setWidth 64, 32⟩ (VG.Proof.CmacAes.Stream.X86.istR s₀) := by
    rw [VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  have hR : VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4 + 6 = 10 ∨ VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4 + 6 = 12 ∨ VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4 + 6 = 14 := by
    rcases hp.klen with h | h | h <;> rw [h] <;> decide
  refine ⟨⟨?_, ⟨esp₇, rd₇, wr₇, by rw [m₇]; exact h.frame⟩⟩, m₇⟩
  exact
  { eax := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
        VG.Proof.CmacAes.Stream.X86.arg_ofNat s₀ 2]
      exact VG.Proof.CmacAes.Stream.X86.rounds32 hp.klen
    edx := by
      rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; rfl
    ebx := u₇.gpr
    rounds := hR
    esp := by rw [esp₇]; exact e48
    wk := by
      rw [VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)]; exact Offset.base_disjoint _ (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
    bW := by rw [esp₇]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact hp.b_st.sub_right kSt
    bS := by rw [esp₇]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega
    fK := by rw [VG.Proof.CmacAes.Stream.X86.add_toNat (by omega)]; omega
    fS := by omega
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.istR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₇, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.CmacAes.Stream.X86.istR s₀, by simp, 240, VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega), by simp⟩
      · exact ⟨VG.Proof.CmacAes.Stream.X86.iscR s₀, by simp, 0, by simp, by simp⟩ }

theorem IMid₂.after {s₀ s s' : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) (h : VG.Proof.CmacAes.Stream.X86.IMid₂ s₀ s)
    (h' : VG.Proof.CmacAes.Stream.X86.SPost s (VG.Proof.CmacAes.Stream.X86.iSt s₀) (VG.Proof.CmacAes.Stream.X86.iSt s₀ + BitVec.ofNat 32 240) (VG.Proof.CmacAes.Stream.X86.iSc s₀) (VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4 + 6) s') : VG.Proof.CmacAes.Stream.X86.IAft s₀ s' := by
  have fr := h'.frame
  rw [h.aft.esp] at fr
  have fSt := hp.fSt
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.aft.esp], by rw [h'.rd, h.aft.rd],
    by rw [h'.wr, h.aft.wr], h.aft.frame.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨VG.Proof.CmacAes.Stream.X86.istR s₀, by simp, ?_⟩
    rw [VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  · exact ⟨VG.Proof.CmacAes.Stream.X86.iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48, by simp, fun _ h => h⟩

theorem sub_after {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) (h : VG.Proof.CmacAes.Stream.X86.IMid₂ s₀ s) :
    WP isa (call4 ("vg_cmac_aes_subkeys" ++ v.suffix) (Impl.CmacAes.X86.subkeys v.callee)) s (VG.Proof.CmacAes.Stream.X86.IAft s₀) :=
  WP.mono ((VG.Proof.CmacAes.Stream.X86.sub_call v) h.args) fun _ h' => h.after hp h'

/-! ## After the calls -/

theorem initPost_eq : initPost = .mov .edx (argOp 0) :: (Impl.CmacAes.X86.zero4 .edx 272 ++ restore 3) := rfl

/-- The chaining value zeroed, and the registers restored from their slots. -/
theorem initPost_wp {s₀ s : State} (hp : VG.Proof.CmacAes.Stream.X86.IPre s₀) (h : VG.Proof.CmacAes.Stream.X86.IAft s₀ s)
    (hs : ∀ r d, (r, d) ∈ saved → s.mem.readW ((VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r) :
    WP isa (.block initPost) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.mem = Proof.Cmac.zero4 s.mem ((VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 272) := by
  have fS : (VG.X86.arg s₀ 3).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (VG.X86.arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  rw [VG.Proof.CmacAes.Stream.X86.initPost_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (hp.keep h.frame (by decide))
    fun s₁ u₁ => ?_
  refine zero4_ok (by decide) (by rw [u₁.gpr]; omega) (by
      rw [u₁.wr, h.wr, hp.wr, u₁.gpr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.istR s₀, by simp, 272, rfl, by simp⟩)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  have hz : Frame [⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩] s.mem s₂.mem := by
    rw [m₂, u₁.mem, u₁.gpr]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.mono (VG.Proof.CmacAes.Stream.X86.restore_wp (s₀ := s₀) (i := 3) (Sc := VG.Proof.CmacAes.Stream.X86.iSc s₀) (by rw [g₂ _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [rd₂, wr₂, u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide))
    (by
      rw [hz.readW (r := ⟨argAddr s₀ 3, 4⟩) (Region.contains_self _ _) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact (hp.a_st.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)]
      exact hp.keep h.frame (by decide))
    fS (by
      rw [rd₂, wr₂, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.iscR s₀, by simp, 0, by simp, by simp⟩)
    fun r d hrd => ?_) fun s' ⟨hcs, hm⟩ => ⟨hcs, by rw [hm, m₂, u₁.mem, u₁.gpr]⟩
  have hb := VG.Proof.CmacAes.Stream.X86.saved_bound _ hrd
  rw [hz.readW (r := ⟨(VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (Offset.sub_base _ (by omega)))
    (by decide)]
  exact hs r d hrd

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  have hp := IPre.of h0
  have fS : (VG.X86.arg s₀ 3).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (VG.X86.arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fSt' : (VG.Proof.CmacAes.Stream.X86.iSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have e48 := hp.esp48
  unfold init
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono ((VG.Proof.CmacAes.Stream.X86.ek_call v) h₁.args) fun s₂ h₂ => ?_)
  have a₂ := h₁.after hp h₂
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86.initMid_wp hp a₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono ((VG.Proof.CmacAes.Stream.X86.sub_call v) h₃.args) fun s₄ h₄ => ?_)
  have a₄ := h₃.after hp h₄
  have f₂ : Frame [⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64, 240⟩, ⟨(VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64, 512⟩, below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48] s₁.mem s₂.mem := by
    have := h₂.frame
    rw [h₁.esp] at this
    refine this.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48, by simp, below_sub (by decide) e48⟩
  have f₄ : Frame [⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64, 2176⟩,
      below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48] s₂.mem s₄.mem := by
    have := h₄.frame; rw [h₃.aft.esp, m₃, VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega)] at this; exact this
  -- The saved registers.
  have dSlot : ∀ d, 2176 ≤ d → d + 4 ≤ 2192 → ∀ r ∈ [⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64, 240⟩, ⟨(VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64, 512⟩,
      below (VG.Proof.CmacAes.Stream.X86.iE s₀) 48, ⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64, 2176⟩],
      (⟨(VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
    have sub : Region.Sub ⟨(VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (VG.Proof.CmacAes.Stream.X86.iscR s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have slots : ∀ r d, (r, d) ∈ saved →
      s₄.mem.readW ((VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := VG.Proof.CmacAes.Stream.X86.saved_bound _ hrd
    have c := Region.contains_self ((VG.Proof.CmacAes.Stream.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₄.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide),
      f₂.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide), h₁.mem]
    exact VG.Proof.CmacAes.Stream.X86.saveMem_slot _ _ _ hrd
  refine WP.mono (VG.Proof.CmacAes.Stream.X86.initPost_wp hp a₄ slots) fun s₅ ⟨hcs, m₅⟩ => ?_
  have fz : Frame [⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have F₅ : Frame (VG.Proof.CmacAes.Stream.X86.IBig s₀) s₀.mem s₅.mem := a₄.frame.trans (fz.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Stream.X86.istR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  refine ⟨⟨hcs, F₅.readW (r := ⟨(VG.Proof.CmacAes.Stream.X86.iE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_s
    · exact VG.Proof.CmacAes.Stream.X86.ret_below e48
  · show Spec.Cmac.Repr s₅.mem ((VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64) (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.iKp s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.iKL s₀)) []
    rw [Proof.Cmac.Stream.repr_iff]
    have hlen : (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.iKp s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.iKL s₀)).length = VG.Proof.CmacAes.Stream.X86.iKL s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    have hkey : Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.Stream.X86.iKp s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.iKL s₀) =
        Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.iKp s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.iKL s₀) := by
      rw [h₁.mem]
      exact Proof.Cmac.bytesAt_frame (VG.Proof.CmacAes.Stream.X86.savedMem_frame _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base _ (by decide))) (by have := hp.fK; omega)
    have dz : ∀ {d n : Nat}, d + n ≤ 272 →
        ∀ r ∈ [(⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩ : Region)],
          (⟨(VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := fun {d n} hd r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 →
        Spec.Aes.bytesAt s₅.mem ((VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 d) n =
          Spec.Aes.bytesAt s₂.mem ((VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [Proof.Cmac.bytesAt_frame fz (dz (by omega)) (by omega), Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_st.sub_right (Offset.sub_base _ (by omega))).symm) (by omega)]
    have hRb : 16 * (Spec.Aes.rounds (VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4) + 1) ≤ 240 := by
      have := hp.klen; simp only [Spec.Aes.rounds]; omega
    have hsch : Spec.Aes.bytesAt s₂.mem ((VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64) (16 * (Spec.Aes.rounds (VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.Stream.X86.iKp s₀).setWidth 64) (VG.Proof.CmacAes.Stream.X86.iKL s₀)) := by rw [h₂.out, hkey]
    have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4) + 1)) (by omega)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem ((VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 =
          Spec.Aes.bytesAt s₄.mem ((VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 :=
        Proof.Cmac.bytesAt_frame fz (dz (d := 240) (n := 32) (by omega)) (by decide)
      rw [show (VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + 240 = (VG.Proof.CmacAes.Stream.X86.iSt s₀).setWidth 64 + BitVec.ofNat 64 240 from rfl, e]
      have o := h₄.out
      rw [VG.Proof.CmacAes.Stream.X86.add_setWidth (by omega), m₃, show VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4 + 6 = Spec.Aes.rounds (VG.Proof.CmacAes.Stream.X86.iKL s₀ / 4) from rfl, hsch] at o
      rw [o]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅]; exact (Proof.Cmac.zero4_bytes _ _).trans rfl

/-! ## Constant time -/

theorem init_rel {s₀ s₀' : State} (h0 : initX86.pre s₀) (h0' : initX86.pre s₀') (hq : initX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  have hp := IPre.of h0
  have hp' := IPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : VG.Proof.CmacAes.Stream.X86.iSt s₀ = VG.Proof.CmacAes.Stream.X86.iSt s₀' := qa 0 (by decide)
  have e1 : VG.Proof.CmacAes.Stream.X86.iKp s₀ = VG.Proof.CmacAes.Stream.X86.iKp s₀' := qa 1 (by decide)
  have e2 : VG.Proof.CmacAes.Stream.X86.iKL s₀ = VG.Proof.CmacAes.Stream.X86.iKL s₀' := by rw [VG.Proof.CmacAes.Stream.X86.iKL, VG.Proof.CmacAes.Stream.X86.iKL, qa 2 (by decide)]
  have e3 : VG.Proof.CmacAes.Stream.X86.iSc s₀ = VG.Proof.CmacAes.Stream.X86.iSc s₀' := qa 3 (by decide)
  have ag : ∀ {a b : State}, VG.Proof.CmacAes.Stream.X86.Pt 4 s₀ a → VG.Proof.CmacAes.Stream.X86.Pt 4 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 4)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := .block initPre) (by taint_decide)).wp (F₁ := VG.Proof.CmacAes.Stream.X86.IMid₁ s₀) (F₂ := VG.Proof.CmacAes.Stream.X86.IMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.X86.initPre_wp hp, VG.Proof.CmacAes.Stream.X86.initPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have e := ((VG.Proof.CmacAes.Stream.X86.ek_rel v (E := VG.Proof.CmacAes.Stream.X86.iE s₀) (P := fun a b => VG.Proof.CmacAes.Stream.X86.IMid₁ s₀ a ∧ VG.Proof.CmacAes.Stream.X86.IMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := VG.Proof.CmacAes.Stream.X86.IAft s₀) (F₂ := VG.Proof.CmacAes.Stream.X86.IAft s₀') fun _ _ h => ⟨(VG.Proof.CmacAes.Stream.X86.ek_after v) hp h.1, (VG.Proof.CmacAes.Stream.X86.ek_after v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.X86.IAft s₀ a ∧ VG.Proof.CmacAes.Stream.X86.IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initMid) (by taint_decide)).wp
    (F₁ := fun s => VG.Proof.CmacAes.Stream.X86.IMid₂ s₀ s) (F₂ := fun s => VG.Proof.CmacAes.Stream.X86.IMid₂ s₀' s)
    fun _ _ h => ⟨WP.mono (VG.Proof.CmacAes.Stream.X86.initMid_wp hp h.1) fun _ h => h.1, WP.mono (VG.Proof.CmacAes.Stream.X86.initMid_wp hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have sk := ((VG.Proof.CmacAes.Stream.X86.sub_rel v (E := VG.Proof.CmacAes.Stream.X86.iE s₀) (P := fun a b => VG.Proof.CmacAes.Stream.X86.IMid₂ s₀ a ∧ VG.Proof.CmacAes.Stream.X86.IMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e2, e3]; exact h.2.args, h.1.aft.esp, by rw [h.2.aft.esp]; exact qE.symm⟩).wp
      (F₁ := VG.Proof.CmacAes.Stream.X86.IAft s₀) (F₂ := VG.Proof.CmacAes.Stream.X86.IAft s₀') fun _ _ h => ⟨(VG.Proof.CmacAes.Stream.X86.sub_after v) hp h.1, (VG.Proof.CmacAes.Stream.X86.sub_after v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.X86.IAft s₀ a ∧ VG.Proof.CmacAes.Stream.X86.IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initPost) (by taint_decide)
  exact a.seq (e.seq (m.seq (sk.seq p)))

theorem init_ct : ConstantTime isa initX86.pre initX86.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((VG.Proof.CmacAes.Stream.X86.init_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.Verified`. -/
section

section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
`esp`, the stack arguments and `ebp`, which the correctness proof pins to a
value of the public arguments (`AAft`), and each call of `vg_cmac_aes_update`,
in its frame, is constant time by its own proof (`upd_rel`), its arguments
pinned by `AMid₁` and `AMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbX86.pre s₀) (h0' : absorbX86.pre s₀')
    (hq : absorbX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee v.suffix) fun _ _ => True := by
  have hp := APre.of h0
  have hp' := APre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have eSt : VG.Proof.CmacAes.Stream.X86.aSt s₀ = VG.Proof.CmacAes.Stream.X86.aSt s₀' := qa 0 (by decide)
  have eR : VG.Proof.CmacAes.Stream.X86.aR s₀ = VG.Proof.CmacAes.Stream.X86.aR s₀' := by rw [VG.Proof.CmacAes.Stream.X86.aR, VG.Proof.CmacAes.Stream.X86.aR, qa 1 (by decide)]
  have eC : VG.Proof.CmacAes.Stream.X86.aC s₀ = VG.Proof.CmacAes.Stream.X86.aC s₀' := by rw [VG.Proof.CmacAes.Stream.X86.aC, VG.Proof.CmacAes.Stream.X86.aC, VG.Proof.CmacAes.Stream.X86.countX86, VG.Proof.CmacAes.Stream.X86.countX86, qa 2 (by decide), qa 3 (by decide)]
  have eD : VG.Proof.CmacAes.Stream.X86.aD s₀ = VG.Proof.CmacAes.Stream.X86.aD s₀' := qa 4 (by decide)
  have eL : VG.Proof.CmacAes.Stream.X86.aL s₀ = VG.Proof.CmacAes.Stream.X86.aL s₀' := by rw [VG.Proof.CmacAes.Stream.X86.aL, VG.Proof.CmacAes.Stream.X86.aL, qa 5 (by decide)]
  have eS : VG.Proof.CmacAes.Stream.X86.aSc s₀ = VG.Proof.CmacAes.Stream.X86.aSc s₀' := qa 6 (by decide)
  have e2 : VG.Proof.CmacAes.Stream.X86.d2Of s₀ = VG.Proof.CmacAes.Stream.X86.d2Of s₀' := by rw [VG.Proof.CmacAes.Stream.X86.d2Of, VG.Proof.CmacAes.Stream.X86.d2Of, eC, eL, eSt, eD]
  have ag : ∀ {rs : List Reg} {a b : State}, VG.Proof.CmacAes.Stream.X86.Pt 7 s₀ a → VG.Proof.CmacAes.Stream.X86.Pt 7 s₀' b → (∀ r ∈ rs, a.gpr r = b.gpr r) →
      VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) a b :=
    fun h₁ h₂ hr => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ hr
  have bp : ∀ {v v' : Nat} {a b : State}, v = v' → VG.Proof.CmacAes.Stream.X86.AAft s₀ v a → VG.Proof.CmacAes.Stream.X86.AAft s₀' v' b → ∀ r ∈ [Reg.ebp], a.gpr r = b.gpr r :=
    fun e h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp, e]
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 7))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _) fun r hr => by simp at hr)
    (c := absorbPre) (by taint_decide)).wp (F₁ := VG.Proof.CmacAes.Stream.X86.AMid₁ s₀) (F₂ := VG.Proof.CmacAes.Stream.X86.AMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.X86.absorbPre_wp hp, VG.Proof.CmacAes.Stream.X86.absorbPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c₁ := ((VG.Proof.CmacAes.Stream.X86.upd_rel v (E := VG.Proof.CmacAes.Stream.X86.aE s₀) (P := fun a b => VG.Proof.CmacAes.Stream.X86.AMid₁ s₀ a ∧ VG.Proof.CmacAes.Stream.X86.AMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eR, eC, eL]; exact h.2.args, h.1.ctx.esp,
        by rw [h.2.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := VG.Proof.CmacAes.Stream.X86.AAft s₀ (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀))) (F₂ := VG.Proof.CmacAes.Stream.X86.AAft s₀' (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀') (VG.Proof.CmacAes.Stream.X86.aL s₀')))
      fun _ _ h => ⟨(VG.Proof.CmacAes.Stream.X86.call1_after v) hp h.1, (VG.Proof.CmacAes.Stream.X86.call1_after v) hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.X86.AAft s₀ (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) a ∧
      VG.Proof.CmacAes.Stream.X86.AAft s₀' (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀') (VG.Proof.CmacAes.Stream.X86.aL s₀')) b) (argTaint [.ebp] (4 + 4 * 7))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2))
    (c := chain2) (by taint_decide)).wp (F₁ := VG.Proof.CmacAes.Stream.X86.AMid₂ s₀) (F₂ := VG.Proof.CmacAes.Stream.X86.AMid₂ s₀')
    fun _ _ h => ⟨WP.mono (VG.Proof.CmacAes.Stream.X86.chain2_mid hp h.1) fun _ h => h.1, WP.mono (VG.Proof.CmacAes.Stream.X86.chain2_mid hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have c₂ := ((VG.Proof.CmacAes.Stream.X86.upd_rel v (E := VG.Proof.CmacAes.Stream.X86.aE s₀) (P := fun a b => VG.Proof.CmacAes.Stream.X86.AMid₂ s₀ a ∧ VG.Proof.CmacAes.Stream.X86.AMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eR, eC, eL, e2]; exact h.2.args, h.1.aft.ctx.esp,
        by rw [h.2.aft.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := VG.Proof.CmacAes.Stream.X86.AAft s₀ (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)))
      (F₂ := VG.Proof.CmacAes.Stream.X86.AAft s₀' (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀') (VG.Proof.CmacAes.Stream.X86.aL s₀') + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀') (VG.Proof.CmacAes.Stream.X86.aL s₀')))
      fun _ _ h => ⟨(VG.Proof.CmacAes.Stream.X86.call2_after v) hp h.1, (VG.Proof.CmacAes.Stream.X86.call2_after v) hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.X86.AAft s₀ (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀) + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀) (VG.Proof.CmacAes.Stream.X86.aL s₀)) a ∧
      VG.Proof.CmacAes.Stream.X86.AAft s₀' (VG.Proof.CmacAes.Stream.X86.fOf (VG.Proof.CmacAes.Stream.X86.aC s₀') (VG.Proof.CmacAes.Stream.X86.aL s₀') + 16 * VG.Proof.CmacAes.Stream.X86.nbOf (VG.Proof.CmacAes.Stream.X86.aC s₀') (VG.Proof.CmacAes.Stream.X86.aL s₀')) b) (argTaint [.ebp] (4 + 4 * 7))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2)) (c := absorbPost) (by taint_decide)
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbX86.pre absorbX86.pub (absorb v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((VG.Proof.CmacAes.Stream.X86.absorb_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86

end

/-!
# Streaming AES-CMAC on x86: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`, with 48 bytes of stack for
`init` (a call of `vg_cmac_aes_subkeys`: its four arguments, the return
address, and its call of `vg_aes_ctr32`) and 56 for `absorb` and `finish` (as
`init`, with six arguments).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem init_spSafe :
    (init v.expand v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [init, call4, Code.all, v.expandSpSafe, Proof.CmacAes.X86.subkeys_spSafe v]
  decide +kernel

theorem absorb_spSafe :
    (absorb v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy,
    chain1, chain2, Code.all, Proof.CmacAes.X86.update_spSafe v]
  decide +kernel

theorem finish_spSafe :
    (finish v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [finish, finPre, call6, countHeld, held, Code.all, Proof.CmacAes.X86.finalize_spSafe v]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition: the state at
`0x1000`, a key of 16 bytes at `0x3000` and the scratch buffer at `0x4000`,
as stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x800c then 16
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x3000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified : Verified X86.target (init v.expand v.callee v.suffix) (initScratchContract X86.abi 48) :=
  Verified.of_correct (fun _ hs => (VG.Proof.CmacAes.Stream.X86.init_wp v) hs) (VG.Proof.CmacAes.Stream.X86.init_ct v) (by
    have a0 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.initSat 0 = 0x1000 := by decide
    have a1 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.initSat 1 = 0x3000 := by decide
    have a2 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.initSat 2 = 16 := by decide
    have a3 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.initSat 3 = 0x4000 := by decide
    have e : argAddr VG.Proof.CmacAes.Stream.X86.initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, VG.Proof.CmacAes.Stream.X86.initX86] [a0, a1, a2, a3, e, esp] using VG.Proof.CmacAes.Stream.X86.initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition: the state at
`0x1000`, 10 rounds, `count` 0, no data at `0x3000` and the scratch buffer
at `0x4000`, as stack arguments at `0x8004`. -/
def absorbSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x8015 then 0x30 else if a = 0x801d then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8004, 28⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified : Verified X86.target (absorb v.callee v.suffix) (absorbScratchContract X86.abi 56) :=
  Verified.of_correct (fun _ hs => (VG.Proof.CmacAes.Stream.X86.absorb_wp v) hs) (VG.Proof.CmacAes.Stream.X86.absorb_ct v) (by
    have a0 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.absorbSat 0 = 0x1000 := by decide
    have a1 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.absorbSat 1 = 10 := by decide
    have a2 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.absorbSat 2 = 0 := by decide
    have a3 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.absorbSat 3 = 0 := by decide
    have a4 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.absorbSat 4 = 0x3000 := by decide
    have a5 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.absorbSat 5 = 0 := by decide
    have a6 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.absorbSat 6 = 0x4000 := by decide
    have e : argAddr VG.Proof.CmacAes.Stream.X86.absorbSat 0 = 0x8004 := by decide
    have esp : absorbSat.gpr .esp = 0x8000 := rfl
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, VG.Proof.CmacAes.Stream.X86.absorbX86, VG.Proof.CmacAes.Stream.X86.countX86] [a0, a1, a2, a3, a4, a5, a6, e, esp] using VG.Proof.CmacAes.Stream.X86.absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition: the state at
`0x1000`, 10 rounds, `count` 0, `out` at `0x2000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def finishSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x8015 then 0x20 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x8004, 24⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified : Verified X86.target (finish v.callee v.suffix) (finishScratchContract X86.abi 56) :=
  Verified.of_correct (fun _ hs => (VG.Proof.CmacAes.Stream.X86.finish_wp v) hs) (VG.Proof.CmacAes.Stream.X86.finish_ct v) (by
    have a0 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.finishSat 0 = 0x1000 := by decide
    have a1 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.finishSat 1 = 10 := by decide
    have a2 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.finishSat 2 = 0 := by decide
    have a3 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.finishSat 3 = 0 := by decide
    have a4 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.finishSat 4 = 0x2000 := by decide
    have a5 : VG.X86.arg VG.Proof.CmacAes.Stream.X86.finishSat 5 = 0x4000 := by decide
    have e : argAddr VG.Proof.CmacAes.Stream.X86.finishSat 0 = 0x8004 := by decide
    have esp : finishSat.gpr .esp = 0x8000 := rfl
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, VG.Proof.CmacAes.Stream.X86.finishX86, VG.Proof.CmacAes.Stream.X86.countX86] [a0, a1, a2, a3, a4, a5, e, esp] using VG.Proof.CmacAes.Stream.X86.finishSat)

end VG.Proof.CmacAes.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame`. -/
section

/-!
# Streaming AES-CMAC on x86, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the copied argument slots (three for `init`, six for `absorb`, five for
`finish`) and the 2304 bytes of working space. The copies are read only
where the pre- and postconditions read the buffers
(`Proof/CmacAes/Stream/Scratch.lean`).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem init_noEsp : (init v.expand v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, call4, Code.allInstrs, VG.Proof.CmacAes.Stream.X86.noEsp_of v.expandNosp,
    VG.Proof.CmacAes.Stream.X86.noEsp_of (Proof.CmacAes.X86.subkeys_nosp v)]
  decide +kernel

theorem absorb_noEsp : (absorb v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy, chain1, chain2,
    Code.allInstrs, VG.Proof.CmacAes.Stream.X86.noEsp_of (Proof.CmacAes.X86.update_nosp v)]
  decide +kernel

theorem finish_noEsp : (finish v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [finish, finPre, call6, countHeld, held, Code.allInstrs,
    VG.Proof.CmacAes.Stream.X86.noEsp_of (Proof.CmacAes.X86.finalize_nosp v)]
  decide +kernel

theorem init_stackUse : stackUse (init v.expand v.callee v.suffix) ≤ 48 := by
  simp only [init, call4, stackUse, v.expandStack, Proof.CmacAes.X86.subkeys_stack v]
  decide +kernel

theorem absorb_stackUse : stackUse (absorb v.callee v.suffix) ≤ 56 := by
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy, chain1, chain2,
    stackUse, Proof.CmacAes.X86.update_stack v]
  decide +kernel

theorem finish_stackUse : stackUse (finish v.callee v.suffix) ≤ 56 := by
  simp only [finish, finPre, call6, countHeld, held, stackUse, Proof.CmacAes.X86.finalize_stack v]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space: the state at `0x1000` and a key of 16 bytes at `0x3000`, as
stack arguments at `0x8004`. -/
def initFrameSat : State :=
  { VG.Proof.CmacAes.Stream.X86.initSat with
                 rd := [⟨0x3000, 16⟩, ⟨0x8004, 12⟩], wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract X86.abi 2372).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.CmacAes.Stream.X86.initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { VG.Proof.CmacAes.Stream.X86.absorbSat with
                   rd := [⟨0x3000, 0⟩, ⟨0x8004, 24⟩], wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86.abi 2392).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [absorbFrameSat, absorbSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.CmacAes.Stream.X86.absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space: as `finishSat`. -/
def finishFrameSat : State :=
  { VG.Proof.CmacAes.Stream.X86.finishSat with
                   rd := [⟨0x8004, 20⟩], wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract X86.abi 2388).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finishFrameSat, finishSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.CmacAes.Stream.X86.finishFrameSat

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2324 3 (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86.abi 2372) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesInitPre X86.abi.ptrBits) (post := Spec.Cmac.aesInitPost X86.abi.ptrBits)
    (wa := false) (stack := 48) (bytes := 2324) (VG.Proof.CmacAes.Stream.X86.init_verified v) (by decide) (VG.Proof.CmacAes.Stream.X86.init_noEsp v)
    (VG.Proof.CmacAes.Stream.X86.init_stackUse v) (initPre_local _) (initPost_local _) VG.Proof.CmacAes.Stream.X86.initFrameSat_pre

theorem absorb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2336 6 (absorb v.callee v.suffix))
      (Spec.Cmac.aesAbsorbContract X86.abi 2392) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesAbsorbPre X86.abi.ptrBits) (post := Spec.Cmac.aesAbsorbPost X86.abi.ptrBits)
    (wa := false) (stack := 56) (bytes := 2336) (VG.Proof.CmacAes.Stream.X86.absorb_verified v) (by decide) (VG.Proof.CmacAes.Stream.X86.absorb_noEsp v)
    (VG.Proof.CmacAes.Stream.X86.absorb_stackUse v) (absorbPre_local _) (absorbPost_local _) VG.Proof.CmacAes.Stream.X86.absorbFrameSat_pre

theorem finish_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2332 5 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86.abi 2388) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesFinishPre X86.abi.ptrBits) (post := Spec.Cmac.aesFinishPost X86.abi.ptrBits)
    (wa := false) (stack := 56) (bytes := 2332) (VG.Proof.CmacAes.Stream.X86.finish_verified v) (by decide) (VG.Proof.CmacAes.Stream.X86.finish_noEsp v)
    (VG.Proof.CmacAes.Stream.X86.finish_stackUse v) (finishPre_local _) (finishPost_local _) VG.Proof.CmacAes.Stream.X86.finishFrameSat_pre

end VG.Proof.CmacAes.Stream.X86

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86

/-- The frame of `withStackScratch` keeps the stack pointer for any `c` that
does, if it does for an empty body (decided for literal sizes). -/
theorem withStackScratch_spSafe {bytes n : Nat} {c : Prog isa}
    (hf : (Impl.StackScratch.X86.withStackScratch bytes n (.block [])).all
      (fun i => !isa.writesSp i) = true)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.StackScratch.X86.withStackScratch bytes n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.StackScratch.X86.withStackScratch, Code.all, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hf ⊢
  simp_all

end VG.Proof.CmacAes.Stream.X86

end
