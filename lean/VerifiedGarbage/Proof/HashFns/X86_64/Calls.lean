module

public import VerifiedGarbage.Spec.HashFns
public import VerifiedGarbage.Proof.Framework.X86_64.CallMeets
public import VerifiedGarbage.Proof.Framework.X86_64.WithConsts
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Hmac.Scratch

/-!
# Calling a table's streaming functions (x86-64)

`init_icall`, `upd_icall` and `fin_icall` call, through `r11`, a hash
function's streaming `init`, `update` and `finalize` (`Spec.HashFns`), as
`FnMeets` says of them in the entry `e` of the caller, as `init_call`,
`upd_call` and `fin_call` (`Proof/Pbkdf2/Md/X86_64/Calls.lean`) call verified
code: from the registers holding their arguments, the call returns in a
state that keeps what the call does not write (`Calls.After`) and `World`,
with the streaming state's new representation. `init_irel`, `upd_irel` and
`fin_irel` are their constant time.
-/

@[expose] public section

namespace VG.Proof.HashFns.X86_64

open VG.X86_64 VG.X86_64.WithConsts
open Spec.HashFns (Streaming)
open Proof.Pbkdf2.Md.X86_64.Calls (After)

theorem callEntry_mem_of {s : State} {x : Addr} (h : ¬ (⟨s.gpr .rsp - 8, 8⟩ : Region).Contains x 1) :
    s.callEntry.mem x = s.mem x := by
  rw [State.callEntry_mem]
  simp only [Mem.writeW, Region.Contains] at h ⊢
  exact Mem.write_apply (by omega)

/-- The tables of constants a call's function reads are held on its entry. -/
theorem held_callEntry {s : State} {n : Nat} {cs : List (String × List (BitVec 64))}
    (held : Abi.constsHeld s.mem s.syms cs)
    (hreg : ∀ t ∈ Abi.constRegions s.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧
      ∀ r ∈ abi.reserved n s.callEntry, t.Disjoint r) :
    Abi.constsHeld s.callEntry.mem s.callEntry.syms cs :=
  constsHeld_congr held (fun t ht => (hreg t ht).1) fun t ht x hx =>
    callEntry_mem_of fun hc => (hreg t ht).2 ⟨s.callEntry.gpr .rsp, 8⟩ (by simp [abi]) x hx
      (by simpa using hc)

theorem ret_disj {s : State} {R : Region} (h : (below (s.gpr .rsp) 16).Disjoint R) :
    (⟨s.gpr .rsp - 8, 8⟩ : Region).Disjoint R := by
  have := Proof.Pbkdf2.Md.X86_64.Calls.ret_sub s
  rw [State.callEntry_rsp] at this
  exact h.sub_left this

theorem stk_disj {s : State} {R : Region} (h : (below (s.gpr .rsp) 16).Disjoint R) :
    (⟨s.gpr .rsp - 8 - 8, 8⟩ : Region).Disjoint R := by
  have := Proof.Pbkdf2.Md.X86_64.Calls.stk_sub s
  rw [State.callEntry_rsp] at this
  exact h.sub_left this

theorem sp8 {s : State} (h : 16 ≤ (s.gpr .rsp).toNat) : 8 ≤ (s.gpr .rsp - 8).toNat := by
  have := Offset.toNat_sub_ofNat (s.gpr .rsp) 8
  simp only [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl] at this ⊢
  rw [this]
  have := (s.gpr .rsp).isLt
  omega

variable (T : Streaming)

theorem init_pre {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hb : st.toNat + T.S.stateBytes ≤ 2 ^ 64) (hsp : 16 ≤ (s.gpr .rsp).toNat)
    (hstk : (below (s.gpr .rsp) 16).Disjoint ⟨st, T.S.stateBytes⟩) :
    (Spec.HashFns.initContract T abi 8).pre (s.callEntry.withRegions [] [⟨st, T.S.stateBytes⟩]) := by
  sig_iff
  sig_reduce [Spec.HashFns.initContract, Spec.HashFns.initSig, abi, argRegs, stackBelow]
  sig_and_intros
  · exact sp8 hsp
  · rfl
  · rw [hdi, Nat.mul_one]
  · trivial
  · rw [hdi, Nat.mul_one]; exact ret_disj hstk
  · rw [hdi, Nat.mul_one]; exact stk_disj hstk
  · rw [hdi, Nat.mul_one]; exact hb
  · trivial

/-- A call of `init` through `r11`, as `FnMeets` says of it in the entry
`e`, of the `S`-byte streaming state at `rdi`. -/
theorem init_icall {stack : Nat} {e s : State}
    (hm : FnMeets abi (fun A n => Spec.HashFns.initContract T A n) 8 stack e (s.gpr .r11))
    (hW : World stack e s) {st : Addr} (hdi : s.gpr .rdi = st)
    (hp : Passes stack 8 e s [] [⟨st, T.S.stateBytes⟩])
    (hb : st.toNat + T.S.stateBytes ≤ 2 ^ 64) (hsp : 16 ≤ (s.gpr .rsp).toNat)
    (hstk : (below (s.gpr .rsp) 16).Disjoint ⟨st, T.S.stateBytes⟩) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st, T.S.stateBytes⟩] s' → World stack e s' → T.S.Repr s'.mem st [] → Q s') :
    WP isa (.icall 8) s Q := by
  refine WP.icallMeets hm hW hp (fun held hreg => ?_) fun s' h₁ h₂ h₃ h₄ hW' ⟨s₂, hm₂, _, hpost⟩ => ?_
  · exact withConsts_pre (sig := Spec.HashFns.initSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.initPost T) (rd₀ := []) rfl (held_callEntry held fun t ht => ⟨(hreg t ht).1,
        (hreg t ht).2.2⟩) (fun t ht => hreg t ht) (init_pre T hdi hb hsp hstk)
  · refine hQ s' ⟨h₁, h₂, h₃, h₄⟩ hW' ?_
    have hp' := withConsts_post (sig := Spec.HashFns.initSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.initPost T) hpost
    sig_reduce [Spec.HashFns.initSig, Spec.HashFns.initPost, abi, argRegs] at hp'
    rw [← hm₂, ← hdi]; exact hp'

/-- The arguments and regions of a call of `update`: the state at `st`, the
`len` bytes at `d` and the working space at `sc`, apart from each other and
from the 16 bytes below `rsp`. -/
structure UArgs (s : State) (st d sc : Addr) (len : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rdx : s.gpr .rdx = d
  rcx : (s.gpr .rcx).toNat = len
  r8 : s.gpr .r8 = sc
  st_sc : Region.Disjoint ⟨st, T.S.stateBytes⟩ ⟨sc, 8 * T.scratch⟩
  d_st : Region.Disjoint ⟨d, len⟩ ⟨st, T.S.stateBytes⟩
  d_sc : Region.Disjoint ⟨d, len⟩ ⟨sc, 8 * T.scratch⟩
  stk_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, T.S.stateBytes⟩
  stk_d : (below (s.gpr .rsp) 16).Disjoint ⟨d, len⟩
  stk_sc : (below (s.gpr .rsp) 16).Disjoint ⟨sc, 8 * T.scratch⟩
  bst : st.toNat + T.S.stateBytes ≤ 2 ^ 64
  bd : d.toNat + len ≤ 2 ^ 64
  bsc : sc.toNat + 8 * T.scratch ≤ 2 ^ 64
  sp : 16 ≤ (s.gpr .rsp).toNat

theorem upd_pre {s : State} {st d sc : Addr} {len : Nat} (h : UArgs T s st d sc len) :
    (Spec.HashFns.updateContract T abi 8).pre
      (s.callEntry.withRegions [⟨d, len⟩] [⟨st, T.S.stateBytes⟩, ⟨sc, 8 * T.scratch⟩]) := by
  sig_iff
  sig_reduce [Spec.HashFns.updateContract, Spec.HashFns.updateSig, abi, argRegs, stackBelow]
  sig_and_intros
  all_goals try simp only [h.rdi, h.rdx, h.r8, h.rcx, Nat.mul_one, Nat.mul_comm T.scratch 8]
  exacts [sp8 h.sp, h.d_st.symm, h.st_sc, h.d_sc, ret_disj h.stk_st, ret_disj h.stk_d, ret_disj h.stk_sc,
    stk_disj h.stk_st, stk_disj h.stk_d, stk_disj h.stk_sc, h.bst, h.bd, h.bsc]

/-- A call of `update` through `r11`, as `FnMeets` says of it in the entry
`e`, of the state at `st` with the `len` bytes at `d` (`UArgs`), after `rsi`
bytes. -/
theorem upd_icall {stack : Nat} {e s : State}
    (hm : FnMeets abi (fun A n => Spec.HashFns.updateContract T A n) 8 stack e (s.gpr .r11))
    (hW : World stack e s) (hR : Proof.Hmac.ReprLocal T.S) {st d sc : Addr} {len : Nat}
    (h : UArgs T s st d sc len) (hp : Passes stack 8 e s [⟨d, len⟩] [⟨st, T.S.stateBytes⟩, ⟨sc, 8 * T.scratch⟩])
    {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st, T.S.stateBytes⟩, ⟨sc, 8 * T.scratch⟩] s' → World stack e s' →
      (∀ m, T.S.Repr s.mem st m → s.gpr .rsi = BitVec.ofNat 64 m.length →
        T.S.Repr s'.mem st (m ++ Spec.Sha256.bytesAt s.mem d len)) → Q s') :
    WP isa (.icall 8) s Q := by
  refine WP.icallMeets hm hW hp (fun held hreg => ?_) fun s' h₁ h₂ h₃ h₄ hW' ⟨s₂, hm₂, _, hpost⟩ => ?_
  · exact withConsts_pre (sig := Spec.HashFns.updateSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.updatePost T) (rd₀ := [⟨d, len⟩]) rfl (held_callEntry held fun t ht =>
        ⟨(hreg t ht).1, (hreg t ht).2.2⟩) (fun t ht => hreg t ht) (upd_pre T h)
  · refine hQ s' ⟨h₁, h₂, h₃, h₄⟩ hW' fun m hr hc => ?_
    have hp' := withConsts_post (sig := Spec.HashFns.updateSig T)
      (pre := fun pb => Curry.const (fun _ => True) _) (post := Spec.HashFns.updatePost T) hpost
    sig_reduce [Spec.HashFns.updateSig, Spec.HashFns.updatePost, abi, argRegs] at hp'
    have e : Spec.Sha256.bytesAt s.callEntry.mem d len = Spec.Sha256.bytesAt s.mem d len := by
      simp only [Spec.Sha256.bytesAt]
      exact List.map_congr_left fun i hi => Proof.Pbkdf2.Md.X86_64.Calls.callEntry_bytes s h.stk_d
        (by have := h.bd; omega) (List.mem_range.mp hi)
    have := hp' m (hR (fun i hi => by
      rw [h.rdi]; exact Proof.Pbkdf2.Md.X86_64.Calls.callEntry_bytes s h.stk_st
        (by have := h.bst; omega) hi) (h.rdi ▸ hr)) (by rw [BitVec.setWidth_eq]; exact hc)
    simp only [BitVec.setWidth_eq, h.rdi, h.rdx, h.rcx, ← State.callEntry_mem, e, hm₂] at this
    exact this

/-- The arguments and regions of a call of `finalize`: the state at `st`, the
`F` bytes at `o` and the working space at `sc`, apart from each other and
from the 16 bytes below `rsp`. -/
structure FArgs (s : State) (st o sc : Addr) : Prop where
  rdi : s.gpr .rdi = st
  rdx : s.gpr .rdx = o
  rcx : s.gpr .rcx = sc
  st_o : Region.Disjoint ⟨st, T.S.stateBytes⟩ ⟨o, T.outBytes⟩
  st_sc : Region.Disjoint ⟨st, T.S.stateBytes⟩ ⟨sc, 8 * T.scratch⟩
  o_sc : Region.Disjoint ⟨o, T.outBytes⟩ ⟨sc, 8 * T.scratch⟩
  stk_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, T.S.stateBytes⟩
  stk_o : (below (s.gpr .rsp) 16).Disjoint ⟨o, T.outBytes⟩
  stk_sc : (below (s.gpr .rsp) 16).Disjoint ⟨sc, 8 * T.scratch⟩
  bst : st.toNat + T.S.stateBytes ≤ 2 ^ 64
  bo : o.toNat + T.outBytes ≤ 2 ^ 64
  bsc : sc.toNat + 8 * T.scratch ≤ 2 ^ 64
  sp : 16 ≤ (s.gpr .rsp).toNat

theorem fin_pre {s : State} {st o sc : Addr} (h : FArgs T s st o sc) :
    (Spec.HashFns.finalizeContract T abi 8).pre
      (s.callEntry.withRegions [] [⟨st, T.S.stateBytes⟩, ⟨o, T.outBytes⟩, ⟨sc, 8 * T.scratch⟩]) := by
  sig_iff
  sig_reduce [Spec.HashFns.finalizeContract, Spec.HashFns.finalizeSig, abi, argRegs, stackBelow]
  sig_and_intros
  all_goals try simp only [h.rdi, h.rdx, h.rcx, Nat.mul_one, Nat.mul_comm T.scratch 8]
  exacts [sp8 h.sp, h.st_o, h.st_sc, h.o_sc, ret_disj h.stk_st, ret_disj h.stk_o, ret_disj h.stk_sc,
    stk_disj h.stk_st, stk_disj h.stk_o, stk_disj h.stk_sc, h.bst, h.bo, h.bsc]

/-- A call of `finalize` through `r11`, as `FnMeets` says of it in the entry
`e`, of the state at `st` of a message of `rsi` bytes, to `o` (`FArgs`). -/
theorem fin_icall {stack : Nat} {e s : State}
    (hm : FnMeets abi (fun A n => Spec.HashFns.finalizeContract T A n) 8 stack e (s.gpr .r11))
    (hW : World stack e s) (hR : Proof.Hmac.ReprLocal T.S) {st o sc : Addr} (h : FArgs T s st o sc)
    (hp : Passes stack 8 e s [] [⟨st, T.S.stateBytes⟩, ⟨o, T.outBytes⟩, ⟨sc, 8 * T.scratch⟩])
    {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st, T.S.stateBytes⟩, ⟨o, T.outBytes⟩, ⟨sc, 8 * T.scratch⟩] s' → World stack e s' →
      (∀ m, T.S.Repr s.mem st m → m.length < 2 ^ 64 → s.gpr .rsi = BitVec.ofNat 64 m.length →
        (Spec.Sha256.bytesAt s'.mem o T.outBytes).take T.S.digestBytes = T.S.H.hash m) → Q s') :
    WP isa (.icall 8) s Q := by
  refine WP.icallMeets hm hW hp (fun held hreg => ?_) fun s' h₁ h₂ h₃ h₄ hW' ⟨s₂, hm₂, _, hpost⟩ => ?_
  · exact withConsts_pre (sig := Spec.HashFns.finalizeSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.finalizePost T) (rd₀ := []) rfl (held_callEntry held fun t ht =>
        ⟨(hreg t ht).1, (hreg t ht).2.2⟩) (fun t ht => hreg t ht) (fin_pre T h)
  · refine hQ s' ⟨h₁, h₂, h₃, h₄⟩ hW' fun m hr hl hc => ?_
    have hp' := withConsts_post (sig := Spec.HashFns.finalizeSig T)
      (pre := fun pb => Curry.const (fun _ => True) _) (post := Spec.HashFns.finalizePost T) hpost
    sig_reduce [Spec.HashFns.finalizeSig, Spec.HashFns.finalizePost, abi, argRegs] at hp'
    have := hp' m (hR (fun i hi => by
      rw [h.rdi]; exact Proof.Pbkdf2.Md.X86_64.Calls.callEntry_bytes s h.stk_st
        (by have := h.bst; omega) hi) (h.rdi ▸ hr)) hl (by rw [BitVec.setWidth_eq]; exact hc)
    simp only [h.rdx, hm₂] at this
    exact this

/-! ## The calls in two runs -/

theorem syms_two {K : Abi isa → Nat → Contract isa} {n stack : Nat} {e₁ e₂ s₁ s₂ : State}
    (tw : TwoRuns K n stack e₁ e₂ s₁ s₂) : s₁.syms = s₂.syms := by
  have := tw.same.2.2
  simp only [abi, Option.elim] at this
  rw [tw.w₁.syms, tw.w₂.syms]
  exact (funext fun x => congrFun this x).symm

theorem upd_pub {s₁ s₂ : State} {st d sc : Addr} {len : Nat} (a₁ : UArgs T s₁ st d sc len)
    (a₂ : UArgs T s₂ st d sc len) (si : s₁.gpr .rsi = s₂.gpr .rsi) (sp : s₁.gpr .rsp = s₂.gpr .rsp)
    (r₁ w₁ r₂ w₂ : List Region) :
    (Spec.HashFns.updateContract T abi 8).pub (s₁.callEntry.withRegions r₁ w₁) (s₂.callEntry.withRegions r₂ w₂) := by
  have cx : s₁.gpr .rcx = s₂.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [a₁.rcx, a₂.rcx])
  unfold Spec.HashFns.updateContract
  rw [Sig.contract_pub_iff]
  sig_reduce [Spec.HashFns.updateContract, Spec.HashFns.updateSig, abi, argRegs]
  sig_and_intros
  all_goals simp only [a₁.rdi, a₂.rdi, a₁.rdx, a₂.rdx, a₁.r8, a₂.r8, si, sp, cx]

theorem init_pub {s₁ s₂ : State} {st : Addr} (d₁ : s₁.gpr .rdi = st) (d₂ : s₂.gpr .rdi = st)
    (sp : s₁.gpr .rsp = s₂.gpr .rsp) (r₁ w₁ r₂ w₂ : List Region) :
    (Spec.HashFns.initContract T abi 8).pub (s₁.callEntry.withRegions r₁ w₁) (s₂.callEntry.withRegions r₂ w₂) := by
  unfold Spec.HashFns.initContract
  rw [Sig.contract_pub_iff]
  sig_reduce [Spec.HashFns.initSig, abi, argRegs]
  sig_and_intros
  all_goals simp only [d₁, d₂, sp]

theorem fin_pub {s₁ s₂ : State} {st o sc : Addr} (a₁ : FArgs T s₁ st o sc) (a₂ : FArgs T s₂ st o sc)
    (si : s₁.gpr .rsi = s₂.gpr .rsi) (sp : s₁.gpr .rsp = s₂.gpr .rsp) (r₁ w₁ r₂ w₂ : List Region) :
    (Spec.HashFns.finalizeContract T abi 8).pub (s₁.callEntry.withRegions r₁ w₁)
      (s₂.callEntry.withRegions r₂ w₂) := by
  unfold Spec.HashFns.finalizeContract
  rw [Sig.contract_pub_iff]
  sig_reduce [Spec.HashFns.finalizeSig, abi, argRegs]
  sig_and_intros
  all_goals simp only [a₁.rdi, a₂.rdi, a₁.rdx, a₂.rdx, a₁.rcx, a₂.rcx, si, sp]

/-- `init`'s call in two runs, each as `init_icall` calls it, of the state
at the same address. -/
theorem init_irel {stack : Nat} {P : State → State → Prop} {st : Addr}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ e₁ e₂,
      TwoRuns (fun A n => Spec.HashFns.initContract T A n) 8 stack e₁ e₂ s₁ s₂ ∧
      Passes stack 8 e₁ s₁ [] [⟨st, T.S.stateBytes⟩] ∧ Passes stack 8 e₂ s₂ [] [⟨st, T.S.stateBytes⟩] ∧
      s₁.gpr .rdi = st ∧ s₂.gpr .rdi = st ∧ st.toNat + T.S.stateBytes ≤ 2 ^ 64 ∧
      16 ≤ (s₁.gpr .rsp).toNat ∧ (below (s₁.gpr .rsp) 16).Disjoint ⟨st, T.S.stateBytes⟩) :
    RelCT isa P (.icall 8) fun _ _ => True := by
  refine RelCT.icallMeets (K := fun A n => Spec.HashFns.initContract T A n) (stack := stack) fun s₁ s₂ hp => ?_
  obtain ⟨e₁, e₂, tw, p₁, p₂, d₁, d₂, hb, hsp, hstk⟩ := h s₁ s₂ hp
  have hsy : s₁.syms = s₂.syms := syms_two tw
  have hsp₂ : 16 ≤ (s₂.gpr .rsp).toNat := by rw [tw.rsp]; exact hsp
  have hstk₂ : (below (s₂.gpr .rsp) 16).Disjoint ⟨st, T.S.stateBytes⟩ := by rw [tw.rsp]; exact hstk
  refine ⟨e₁, e₂, _, _, _, _, tw, p₁, p₂, fun held₁ held₂ hreg₁ hreg₂ => ⟨?_, ?_, ?_⟩⟩
  · exact withConsts_pre (sig := Spec.HashFns.initSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.initPost T) (rd₀ := []) rfl (held_callEntry held₁ fun t ht =>
        ⟨(hreg₁ t ht).1, (hreg₁ t ht).2.2⟩) (fun t ht => hreg₁ t ht) (init_pre T d₁ hb hsp hstk)
  · exact withConsts_pre (sig := Spec.HashFns.initSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.initPost T) (rd₀ := []) rfl (held_callEntry held₂ fun t ht =>
        ⟨(hreg₂ t ht).1, (hreg₂ t ht).2.2⟩) (fun t ht => hreg₂ t ht) (init_pre T d₂ hb hsp₂ hstk₂)
  · exact withConsts_pub' (sig := Spec.HashFns.initSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.initPost T) hsy (init_pub T d₁ d₂ tw.rsp.symm _ _ _ _)

/-- `update`'s call in two runs, each as `upd_icall` calls it, with the same
arguments. -/
theorem upd_irel {stack : Nat} {P : State → State → Prop} {st d sc : Addr} {len : Nat}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ e₁ e₂,
      TwoRuns (fun A n => Spec.HashFns.updateContract T A n) 8 stack e₁ e₂ s₁ s₂ ∧
      Passes stack 8 e₁ s₁ [⟨d, len⟩] [⟨st, T.S.stateBytes⟩, ⟨sc, 8 * T.scratch⟩] ∧
      Passes stack 8 e₂ s₂ [⟨d, len⟩] [⟨st, T.S.stateBytes⟩, ⟨sc, 8 * T.scratch⟩] ∧
      UArgs T s₁ st d sc len ∧ UArgs T s₂ st d sc len ∧ s₁.gpr .rsi = s₂.gpr .rsi) :
    RelCT isa P (.icall 8) fun _ _ => True := by
  refine RelCT.icallMeets (K := fun A n => Spec.HashFns.updateContract T A n) (stack := stack) fun s₁ s₂ hp => ?_
  obtain ⟨e₁, e₂, tw, p₁, p₂, a₁, a₂, si⟩ := h s₁ s₂ hp
  have hsy : s₁.syms = s₂.syms := syms_two tw
  refine ⟨e₁, e₂, _, _, _, _, tw, p₁, p₂, fun held₁ held₂ hreg₁ hreg₂ => ⟨?_, ?_, ?_⟩⟩
  · exact withConsts_pre (sig := Spec.HashFns.updateSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.updatePost T) (rd₀ := [⟨d, len⟩]) rfl (held_callEntry held₁ fun t ht =>
        ⟨(hreg₁ t ht).1, (hreg₁ t ht).2.2⟩) (fun t ht => hreg₁ t ht) (upd_pre T a₁)
  · exact withConsts_pre (sig := Spec.HashFns.updateSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.updatePost T) (rd₀ := [⟨d, len⟩]) rfl (held_callEntry held₂ fun t ht =>
        ⟨(hreg₂ t ht).1, (hreg₂ t ht).2.2⟩) (fun t ht => hreg₂ t ht) (upd_pre T a₂)
  · exact withConsts_pub' (sig := Spec.HashFns.updateSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.updatePost T) hsy (upd_pub T a₁ a₂ si tw.rsp.symm _ _ _ _)

/-- `finalize`'s call in two runs, each as `fin_icall` calls it, with the same
arguments. -/
theorem fin_irel {stack : Nat} {P : State → State → Prop} {st o sc : Addr}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ e₁ e₂,
      TwoRuns (fun A n => Spec.HashFns.finalizeContract T A n) 8 stack e₁ e₂ s₁ s₂ ∧
      Passes stack 8 e₁ s₁ [] [⟨st, T.S.stateBytes⟩, ⟨o, T.outBytes⟩, ⟨sc, 8 * T.scratch⟩] ∧
      Passes stack 8 e₂ s₂ [] [⟨st, T.S.stateBytes⟩, ⟨o, T.outBytes⟩, ⟨sc, 8 * T.scratch⟩] ∧
      FArgs T s₁ st o sc ∧ FArgs T s₂ st o sc ∧ s₁.gpr .rsi = s₂.gpr .rsi) :
    RelCT isa P (.icall 8) fun _ _ => True := by
  refine RelCT.icallMeets (K := fun A n => Spec.HashFns.finalizeContract T A n) (stack := stack) fun s₁ s₂ hp => ?_
  obtain ⟨e₁, e₂, tw, p₁, p₂, a₁, a₂, si⟩ := h s₁ s₂ hp
  have hsy : s₁.syms = s₂.syms := syms_two tw
  refine ⟨e₁, e₂, _, _, _, _, tw, p₁, p₂, fun held₁ held₂ hreg₁ hreg₂ => ⟨?_, ?_, ?_⟩⟩
  · exact withConsts_pre (sig := Spec.HashFns.finalizeSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.finalizePost T) (rd₀ := []) rfl (held_callEntry held₁ fun t ht =>
        ⟨(hreg₁ t ht).1, (hreg₁ t ht).2.2⟩) (fun t ht => hreg₁ t ht) (fin_pre T a₁)
  · exact withConsts_pre (sig := Spec.HashFns.finalizeSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.finalizePost T) (rd₀ := []) rfl (held_callEntry held₂ fun t ht =>
        ⟨(hreg₂ t ht).1, (hreg₂ t ht).2.2⟩) (fun t ht => hreg₂ t ht) (fin_pre T a₂)
  · exact withConsts_pub' (sig := Spec.HashFns.finalizeSig T) (pre := fun pb => Curry.const (fun _ => True) _)
      (post := Spec.HashFns.finalizePost T) hsy (fin_pub T a₁ a₂ si tw.rsp.symm _ _ _ _)

end VG.Proof.HashFns.X86_64
