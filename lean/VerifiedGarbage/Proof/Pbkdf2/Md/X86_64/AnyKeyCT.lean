module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKey
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# HMAC's `init` for a key of any length over any Merkle–Damgård hash function on x86-64: constant time, verified

The pieces between the calls are checked by the taint analysis: the entry
(`AnyOK.entry`, for each hash function), and the pieces `pbkdf2` shares
(`Pbk.Checks`: the key's, and the exit), each from registers that the
correctness proof fixes to public values (`KE`, `KR`). The calls are
constant time by their callees' proofs, and the branch on the key's length
goes the same way in both runs. `hmacInitAny_verified` puts it together for
each hash function, from what the kernel checks of its code (`CoreOK`,
`AnyOK`) and of the functions it calls (`Callees`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Any

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK CoreOK Callees core nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Pbk (PSizes layout end_le L_lt hinit_rel eregs kregs)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG rel_taint rel_wp PubEq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash)

variable {H : Hash}

/-! ## What agrees in the two runs -/

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem scr_eq : scr s₀' = scr s₀ := hq.r8.symm
theorem A_eq (o : Nat) : A s₀' o = A s₀ o := by show scr s₀' + _ = scr s₀ + _; rw [scr_eq hq]
theorem key_eq : key s₀' = key s₀ := hq.rdx.symm
theorem kln_eq : kln s₀' = kln s₀ := by show (s₀'.gpr .rcx).toNat = _; rw [← hq.rcx]
theorem kp_eq : kp H s₀' = kp H s₀ := by
  show (if kln s₀' < H.P.B + 1 then key s₀' else A s₀' H.hkO) = _; rw [kln_eq hq, key_eq hq, A_eq hq]
theorem kl_eq : kl H s₀' = kl H s₀ := by
  show (if kln s₀' < H.P.B + 1 then kln s₀' else H.D) = _; rw [kln_eq hq]

theorem kr_agree {s s' : State} (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.r15, h'.r15, scr_eq hq]
  · rw [h.rsp, h'.rsp, hq.rsp]

theorem ke_agree {s s' : State} (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') :
    ∀ r ∈ eregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, key_eq hq]
  · rw [h.rbp, h'.rbp, hq.rcx]
  · rw [h.r12, h'.r12]; exact hq.rdi
  · rw [h.r13, h'.r13]; exact hq.rsi
  · exact kr_agree hq h.kr h'.kr _ (by simp)
  · exact kr_agree hq h.kr h'.kr _ (by simp)

theorem ke_rsp {s s' : State} (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') : s.gpr .rsp = s'.gpr .rsp :=
  ke_agree hq h h' _ (by simp)

end

/-! ## The pieces in two runs -/

/-- The taint check of `initAny`'s entry, the piece `pbkdf2` does not have. -/
abbrev EntryCheck (H : Hash) : Prop :=
  ∃ hc, (Taint.check taint (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) (.block H.anyEntry) hc).isSome = true

/-- The taint check of the arguments of HMAC's `init`. -/
abbrev ArgsCheck : Prop :=
  ∃ hc, (Taint.check taint (Taint.ofRegs eregs) (.block Hash.anyArgs) hc).isSome = true

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : Pre (H := H) s₀) (hp' : Pre (H := H) s₀') (hz : PSizes H)
  (hq : PubEq s₀ s₀') (hc : Pbk.Checks H)
include hH hp hp' hz hq hc

omit hH hc in
theorem entry_rel (he : EntryCheck H) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.anyEntry)
    fun s s' => (KE (H := H) s₀ s ∧ s.cf = some (decide (kln s₀ < H.P.B + 1))) ∧
      (KE (H := H) s₀' s' ∧ s'.cf = some (decide (kln s₀' < H.P.B + 1))) :=
  rel_taint (F := fun s => s = s₀) (F' := fun s => s = s₀') [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]
    (fun s s' e e' r hr => by
      rw [e, e']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hq.rdi
      · exact hq.rsi
      · exact hq.rdx
      · exact hq.rcx
      · exact hq.r8
      · exact hq.rsp) he
    (fun _ e => by rw [e]; exact entry_ok hp hz) (fun _ e => by rw [e]; exact entry_ok hp' hz)

/-- Hashing a key longer than a block. -/
theorem hashKey_rel : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.hashKey
    fun _ _ => True := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  unfold Hash.hashKey
  have r₁ := rel_taint (G := fun t => KE (H := H) s₀ t ∧ t.gpr .rdi = A s₀ H.stWO)
    (G' := fun t => KE (H := H) s₀' t ∧ t.gpr .rdi = A s₀' H.stWO) eregs ag hc.hk1
    (fun _ h => hk1_ok hz h) (fun _ h => hk1_ok hz h)
  have ini : ∀ {σ₀ s : State}, Pre (H := H) σ₀ → KE (H := H) σ₀ s →
      Covers [⟨A σ₀ H.stWO, H.S⟩] s.wr ∧ (below (s.gpr .rsp) 16).Disjoint ⟨A σ₀ H.stWO, H.S⟩ :=
    fun hp h => ⟨Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by omega),
      stk_sc hp h.kr (by omega) (part_sub (by omega))⟩
  have c₂ := rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.init_rel hH.stream (st := A s₀ H.stWO)
      (P := fun s s' => (KE (H := H) s₀ s ∧ s.gpr .rdi = A s₀ H.stWO) ∧
        (KE (H := H) s₀' s' ∧ s'.gpr .rdi = A s₀' H.stWO))
      fun s s' h => by
        have i := ini hp h.1.1; have i' := ini hp' h.2.1
        rw [A_eq hq] at i' h
        exact ⟨h.1.2, h.2.2, i.1, i'.1, i.2, i'.2, ke_rsp hq h.1.1 h.2.1⟩)
    (fun _ h => hk2_ok hp hz hH h.1 h.2) (fun _ h => hk2_ok hp' hz hH h.1 h.2)
  have r₃ := rel_taint (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [])
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) []) eregs
    (fun s s' h h' => ag s s' h.1 h'.1) hc.hk3
    (fun _ h => hk3_ok hp hz hH h.1 h.2) (fun _ h => hk3_ok hp' hz hH h.1 h.2)
  have r₅ := rel_taint
    (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) (bytesAt s₀'.mem (key s₀') (kln s₀')))
    eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.hk5
    (fun _ h => hk5_ok hp hz hH h.1 h.2) (fun _ h => hk5_ok hp' hz hH h.1 h.2)
  have r₇ := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (key s₀) (kln s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧
      bytesAt t.mem (A s₀' H.hkO) H.D = hH.SH.H.hash (bytesAt s₀'.mem (key s₀') (kln s₀')))
    eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.hk7
    (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial) (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial)
  refine (r₁.seq (c₂.seq (r₃.seq (RelCT.seq ?_ (r₅.seq (RelCT.seq ?_ r₇)))))).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, key_eq hq, scr_eq hq, kln_eq hq] at a'
          exact ⟨a, a', by rw [i, i'], ke_rsp hq k k'⟩)
        (fun _ h => hk4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => hk4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.fin_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, A_eq hq, scr_eq hq] at a'
          exact ⟨a, a', by rw [i, i', hq.rcx], ke_rsp hq k k'⟩)
        (fun _ h => hk6_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => hk6_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- The key. -/
theorem key_rel : RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.cf = some (decide (kln s₀ < H.P.B + 1))) ∧
      (KE (H := H) s₀' s' ∧ s'.cf = some (decide (kln s₀' < H.P.B + 1)))) H.key
    fun s s' => (KE (H := H) s₀ s ∧ s.gpr .rdx = kp H s₀ ∧ (s.gpr .rcx).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .rdx = kp H s₀' ∧ (s'.gpr .rcx).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀')) := by
  have ite : RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.cf = some (decide (kln s₀ < H.P.B + 1))) ∧
      (KE (H := H) s₀' s' ∧ s'.cf = some (decide (kln s₀' < H.P.B + 1)))) H.key fun _ _ => True := by
    unfold Hash.key
    refine RelCT.ite (fun s s' h => by simp [eval, h.1.2, h.2.2, kln_eq hq]) ?_ ?_
    · exact (hashKey_rel hH hp hp' hz hq hc).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · obtain ⟨_, hs⟩ := hc.short
      exact RelCT.taint (A := taint) (Taint.ofRegs eregs)
        (fun _ _ h => Taint.agree_ofRegs (ke_agree hq h.1.1.1 h.1.2.1)) hs
  exact (ite.wp fun s s' h => ⟨key_ok hp hz hH h.1.1 h.1.2, key_ok hp' hz hH h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

omit hc in
/-- HMAC's `init`, with its arguments. -/
theorem init_rel (ha : ArgsCheck) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) :
    RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.gpr .rdx = kp H s₀ ∧ (s.gpr .rcx).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .rdx = kp H s₀' ∧ (s'.gpr .rcx).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀')))
      (.seq (.block Hash.anyArgs) (.call H.hmacInitN H.hmacInit))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  have r₁ := rel_taint
    (F := fun s => KE (H := H) s₀ s ∧ s.gpr .rdx = kp H s₀ ∧ (s.gpr .rcx).toNat = kl H s₀ ∧
      KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀))
    (F' := fun s => KE (H := H) s₀' s ∧ s.gpr .rdx = kp H s₀' ∧ (s.gpr .rcx).toNat = kl H s₀' ∧
      KeyAt hH s₀' s.mem (kp H s₀') (kl H s₀'))
    eregs (fun s s' h h' => ke_agree hq h.1 h'.1) ha
    (fun _ h => args_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => args_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  refine r₁.seq ((rel_wp (hinit_rel hH hI fun s s' h => by
        obtain ⟨⟨k, a, -⟩, ⟨k', a', -⟩⟩ := h
        rw [kp_eq hq, scr_eq hq, kl_eq hq, show inn s₀' = inn s₀ from hq.rdi.symm,
          show out s₀' = out s₀ from hq.rsi.symm] at a'
        exact ⟨a, a', ke_rsp hq k k'⟩)
      (fun _ h => call_ok hp hz hH hI hIsp hId h.1 h.2.1 h.2.2)
      (fun _ h => call_ok hp' hz hH hI hIsp hId h.1 h.2.1 h.2.2)).mono (fun _ _ h => h)
    fun _ _ h => ⟨h.1.1, h.2.1⟩)

theorem ct (he : EntryCheck H) (ha : ArgsCheck) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInitAny fun _ _ => True := by
  unfold Hash.hmacInitAny
  obtain ⟨_, hx⟩ := hc.exit
  have ex : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.exit) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1 h.2)) hx
  exact (entry_rel hp hp' hz hq he).seq ((key_rel hH hp hp' hz hq hc).seq
    (RelCT.assoc ((init_rel hH hp hp' hz hq ha hI hIsp hId).seq ex)))

end

/-- `initAny` is verified against `anyG`, given the taint checks, the proof
of HMAC's `init`, and the facts about its code that the kernel checks for
each hash function. -/
theorem verified (hH : HashOK H) (hz : PSizes H) (hc : Pbk.Checks H) (he : EntryCheck H) (ha : ArgsCheck)
    (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hIsp : NoSp H.hmacInit)
    (hId : H.hmacInit.depth ≤ 2)
    (hmx : H.hmacInitAny.allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (anyG hH.SH (H.W + H.S)).pre s) :
    Verified X86_64.target H.hmacInitAny (anyG hH.SH (H.W + H.S)) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he', hg, hpost⟩ := correct (pre_of hH hs) hz hH hI hIsp hId
    exact ⟨t, s', he', abiPreserved_of_exec hmx he' hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH h₁) (pre_of hH h₂) hz ⟨h1, h2, h3, h4, h5, h6⟩ hc he ha hI hIsp hId
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## For each hash function -/

/-- What the kernel checks of `initAny`'s own code (`core H`), once for each
hash function: the taint checks of its entry and of HMAC's `init`'s
arguments, that no instruction loads MXCSR
or writes `rsp`, and the stack it uses without that of its callees'
callees. -/
structure AnyOK (C : Hash) : Prop where
  entry : EntryCheck C
  args : ArgsCheck
  mx : C.hmacInitAny.allInstrs (fun i => !loadsMxcsr i) = true
  sp : C.hmacInitAny.allInstrs (fun i => !isa.writesSp i) = true
  xd : C.hmacInitAny.x86_64Depth ≤ 24

section
variable {p : Instr → Bool} (hc : H.compC.allInstrs p = true) (hi : H.initC.allInstrs p = true)
include hc hi

theorem core_hmacInitAny (h : (core H).hmacInitAny.allInstrs p = true) : H.hmacInitAny.allInstrs p = true := by
  simp only [Hash.hmacInitAny, Hash.key, Hash.hashKey, Hash.hmacInit, Hash.initKeys, Hash.updC, Hash.finC,
    Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callInit,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.allInstrs, hc, hi, Bool.and_true, Bool.true_and] at h ⊢
  exact h

end

theorem core_hmacInitAny_xdepth (hc : H.compC.x86_64Depth = 0) (hi : H.initC.x86_64Depth = 0)
    (h : (core H).hmacInitAny.x86_64Depth ≤ 24) : H.hmacInitAny.x86_64Depth ≤ 24 := by
  simp only [Hash.hmacInitAny, Hash.key, Hash.hashKey, Hash.hmacInit, Hash.initKeys, Hash.updC, Hash.finC,
    Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callInit,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.x86_64Depth, hc, hi] at h ⊢
  exact h

section
variable {H : Hash} (hH : HashOK H) (C : CoreOK (core H)) (A : AnyOK (core H)) (K : Callees H)
include hH C A K

/-- `initAny`, verified against `anyG`. -/
theorem hmacInitAny_ok
    (hsI : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s)
    (hsat : ∃ s, (anyG hH.SH (H.W + H.S)).pre s) :
    Verified X86_64.target H.hmacInitAny (anyG hH.SH (H.W + H.S)) :=
  verified hH hH.psizes (Pbk.Checks.of_core C.pbk) A.entry A.args (VG.Proof.Pbkdf2.Md.X86_64.hmacInit_ok hH C K hsI)
    (nosp_of (VG.Proof.Pbkdf2.Md.X86_64.core_hmacInit K.cNs K.iNs C.hinitNs))
    (VG.Proof.Pbkdf2.Md.X86_64.core_hmacInit_depth K.cD K.iD C.hinitD)
    (core_hmacInitAny K.cMx K.iMx A.mx) hsat

omit hH C in
theorem hmacInitAny_sp : H.hmacInitAny.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_hmacInitAny K.cSp K.iSp A.sp)

omit hH C in
theorem hmacInitAny_xd : H.hmacInitAny.x86_64Depth ≤ 24 := core_hmacInitAny_xdepth K.cXD K.iXD A.xd

end

/-! ## The shared contract -/

/-- `VG.Spec.Hmac.initAnyKeyContract` with its working space (`W` words) as
an argument (as `Proof.Hmac.initScratchContract` is `initContract`'s), and
calls two deep below its own: the contract that the function allocating the
working space follows from (`Verified.stackScratchWiped`). -/
def anyScratchContract (S : StreamingHash) (W : Nat) : Contract isa :=
  (Proof.Hmac.initScratchSig S W).contract X86_64.abi
    (post := fun inner outer key keyLen _scratch => Spec.Hmac.initPost S X86_64.abi.ptrBits inner outer key keyLen)
    (writeArgs := true) (stack := 24)

/-- `anyG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem anyImp (S : StreamingHash) (W : Nat) (h : ∃ s, (anyScratchContract S W).pre s) :
    (anyG S W).Implies (anyScratchContract S W) := by
  generic_implies [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, anyG, X86_64.abi,
    X86_64.argRegs] using h

section
variable {H : Hash} (hH : HashOK H) (C : CoreOK (core H)) (A : AnyOK (core H)) (K : Callees H)
include hH C A K

/-- `initAny`, verified against the shared contract. -/
theorem hmacInitAny_verified
    (hsI : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s)
    (hsat : ∃ s, (anyScratchContract hH.SH (H.W + H.S)).pre s) :
    Verified X86_64.target H.hmacInitAny (anyScratchContract hH.SH (H.W + H.S)) :=
  (hmacInitAny_ok hH C A K hsI (anyImp _ _ hsat).sat_left).of_implies (anyImp _ _ hsat)

end

end VG.Proof.Pbkdf2.Md.X86_64.Any
