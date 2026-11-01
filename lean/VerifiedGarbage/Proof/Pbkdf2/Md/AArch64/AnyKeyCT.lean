module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKey
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# HMAC's `init` for a key of any length over any Merkle–Damgård hash function on AArch64: constant time, verified

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/AnyKeyCT.lean`): the pieces between the
calls are checked by the taint analysis: the entry and HMAC's `init`'s
arguments (`AnyOK`, for each hash function), and the pieces `pbkdf2` shares
(`Pbk.Checks`: the key's, and the exit), each from registers that the
correctness proof fixes to public values (`KE`, `KR`). The calls are
constant time by their callees' proofs, and the branches on the key's length
go the same way in both runs. `hmacInitAny_verified` puts it together for
each hash function, verified against the shared contract.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Any

open VG.AArch64
open VG.Proof.MdStream.AArch64 (wp_lsr wp_subImm)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK CoreOK core)
open VG.Proof.Pbkdf2.Md.AArch64.Pbk (PSizes layout end_le hinit_rel epub log2_B)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG rel_taint rel_wp PubEq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash)

variable {H : Hash}

/-! ## The key's branches, one run at a time -/

section
variable {s₀ : State} (hz : PSizes H)
include hz

theorem keyShr_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.keyShr) s fun t =>
      KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀ < H.P.B)) := by
  unfold Hash.keyShr
  exact wp_lsr (log2_B hz).2 fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), key_shr hz h u₁⟩

theorem keySub_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.keySub) s fun t =>
      KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀ = H.P.B)) := by
  have hB := hz.B_le
  unfold Hash.keySub
  exact wp_subImm (by omega) fun s₂ u₂ => WP.block_nil ⟨h.upd u₂ (by decide), key_sub h u₂ (by omega)⟩

end

/-! ## What agrees in the two runs -/

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem scr_eq : scr s₀' = scr s₀ := hq.x4.symm
theorem A_eq (o : Nat) : A s₀' o = A s₀ o := by show scr s₀' + _ = scr s₀ + _; rw [scr_eq hq]
theorem key_eq : key s₀' = key s₀ := hq.x2.symm
theorem kln_eq : kln s₀' = kln s₀ := by show (s₀'.gpr .x3).toNat = _; rw [← hq.x3]
theorem kp_eq : kp H s₀' = kp H s₀ := by
  show (if kln s₀' < H.P.B + 1 then key s₀' else A s₀' H.hkO) = _; rw [kln_eq hq, key_eq hq, A_eq hq]
theorem kl_eq : kl H s₀' = kl H s₀ := by
  show (if kln s₀' < H.P.B + 1 then kln s₀' else H.D) = _; rw [kln_eq hq]

theorem kr_agree {s s' : State} (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ [Reg.x23], s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr; rw [h.x23, h'.x23, scr_eq hq]

theorem ke_agree {s s' : State} (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ epub, s.gpr r = s'.gpr r := by
  refine ⟨(kr_agree hq h.kr h'.kr).1, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, key_eq hq]
  · rw [h.x20, h'.x20, hq.x3]
  · rw [h.x21, h'.x21]; exact hq.x0
  · rw [h.x22, h'.x22]; exact hq.x1
  · exact (kr_agree hq h.kr h'.kr).2 _ (by simp)

end

/-! ## The pieces in two runs -/

/-- The taint check of `initAny`'s entry, the piece `pbkdf2` does not have. -/
abbrev EntryCheck (H : Hash) : Prop :=
  ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Calls.args) (.block H.anyEntry) hc).isSome = true

/-- The taint check of the arguments of HMAC's `init`. -/
abbrev ArgsCheck : Prop :=
  ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block Hash.anyArgs) hc).isSome = true

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : Pre (H := H) s₀) (hp' : Pre (H := H) s₀') (hz : PSizes H)
  (hq : PubEq s₀ s₀') (hc : Pbk.Checks H)
include hH hp hp' hz hq hc

omit hH hc in
theorem entry_rel (he : EntryCheck H) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.anyEntry)
      fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s' :=
  rel_taint VG.Proof.Pbkdf2.Md.AArch64.Calls.args (fun s s' e e' => by
      rw [e, e']
      refine ⟨hq.sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hq.x0, hq.x1, hq.x2, hq.x3, hq.x4]) he
    (fun _ e => by rw [e]; exact entry_ok hp hz) (fun _ e => by rw [e]; exact entry_ok hp' hz)

/-- Hashing a key longer than a block. -/
theorem hashKey_rel : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.hashKey
    fun _ _ => True := by
  have hl := layout (H := H); have he := end_le hz
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  unfold Hash.hashKey
  have r₁ := rel_taint (G := fun t => KE (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.stWO)
    (G' := fun t => KE (H := H) s₀' t ∧ t.gpr .x0 = A s₀' H.stWO) epub ag hc.hk1
    (fun _ h => hk1_ok hz h) (fun _ h => hk1_ok hz h)
  have ini : ∀ {σ₀ s : State}, Pre (H := H) σ₀ → KE (H := H) σ₀ s →
      Covers [⟨A σ₀ H.stWO, H.stream.S⟩] s.wr :=
    fun hp h => Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by omega)
  have c₂ := rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.init_rel hH.stream (st := A s₀ H.stWO)
      (P := fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x0 = A s₀ H.stWO) ∧
        (KE (H := H) s₀' s' ∧ s'.gpr .x0 = A s₀' H.stWO))
      fun s s' h => by
        have i := ini hp h.1.1; have i' := ini hp' h.2.1
        rw [A_eq hq] at i' h
        exact ⟨h.1.2, h.2.2, i, i', (ke_agree hq h.1.1 h.2.1).1⟩)
    (fun _ h => hk2_ok hp hz hH h.1 h.2) (fun _ h => hk2_ok hp' hz hH h.1 h.2)
  have r₃ := rel_taint (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [])
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) []) epub
    (fun s s' h h' => ag s s' h.1 h'.1) hc.hk3
    (fun _ h => hk3_ok hp hz hH h.1 h.2) (fun _ h => hk3_ok hp' hz hH h.1 h.2)
  have r₅ := rel_taint
    (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (key s₀) (kln s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) (bytesAt s₀'.mem (key s₀') (kln s₀')))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.hk5
    (fun _ h => hk5_ok hp hz hH h.1 h.2) (fun _ h => hk5_ok hp' hz hH h.1 h.2)
  have r₇ := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (key s₀) (kln s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧
      bytesAt t.mem (A s₀' H.hkO) H.D = hH.SH.H.hash (bytesAt s₀'.mem (key s₀') (kln s₀')))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.hk7
    (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial) (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial)
  refine (r₁.seq (c₂.seq (r₃.seq (RelCT.seq ?_ (r₅.seq (RelCT.seq ?_ r₇)))))).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, key_eq hq, scr_eq hq, kln_eq hq] at a'
          exact ⟨a, a', by rw [i, i'], (ke_agree hq k k').1⟩)
        (fun _ h => hk4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => hk4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.fin_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, A_eq hq, scr_eq hq] at a'
          exact ⟨a, a', by rw [i, i', hq.x3], (ke_agree hq k k').1⟩)
        (fun _ h => hk6_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => hk6_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- The key. -/
theorem key_rel : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.key
    fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .x2 = kp H s₀' ∧ (s'.gpr .x3).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀')) := by
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  obtain ⟨_, hs⟩ := hc.short
  have short : ∀ {P : State → State → Prop}, (∀ s s', P s s' → KE (H := H) s₀ s ∧ KE (H := H) s₀' s') →
      RelCT isa P (.block Hash.short) fun _ _ => True := fun hP =>
    RelCT.taint (A := taint) (Taint.ofRegs epub) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := ke_agree hq (hP _ _ h).1 (hP _ _ h).2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hs
  have ite : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.key fun _ _ => True := by
    unfold Hash.key
    have r₁ := rel_taint
      (G := fun t => KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀ < H.P.B)))
      (G' := fun t => KE (H := H) s₀' t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀' < H.P.B)))
      epub ag hc.keyShr (fun _ h => keyShr_ok hz h) (fun _ h => keyShr_ok hz h)
    refine r₁.seq (RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, kln_eq hq])
      (short fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_)
    have r₂ := rel_taint
      (F := fun t => KE (H := H) s₀ t) (F' := fun t => KE (H := H) s₀' t)
      (G := fun t => KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀ = H.P.B)))
      (G' := fun t => KE (H := H) s₀' t ∧ isa.eval (.zero .x .x9) t = some (decide (kln s₀' = H.P.B)))
      epub ag hc.keySub (fun _ h => keySub_ok hz h) (fun _ h => keySub_ok hz h)
    refine (r₂.seq (RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, kln_eq hq])
      (short fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    exact (hashKey_rel hH hp hp' hz hq hc).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  exact (ite.wp fun s s' h => ⟨key_ok hp hz hH h.1, key_ok hp' hz hH h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

omit hc in
/-- HMAC's `init`, with its arguments. -/
theorem init_rel (ha : ArgsCheck) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) :
    RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .x2 = kp H s₀' ∧ (s'.gpr .x3).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀')))
      (.seq (.block Hash.anyArgs) (.call H.hmacInitN H.hmacInit))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  have r₁ := rel_taint
    (F := fun s => KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
      KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀))
    (F' := fun s => KE (H := H) s₀' s ∧ s.gpr .x2 = kp H s₀' ∧ (s.gpr .x3).toNat = kl H s₀' ∧
      KeyAt hH s₀' s.mem (kp H s₀') (kl H s₀'))
    epub (fun s s' h h' => ke_agree hq h.1 h'.1) ha
    (fun _ h => args_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => args_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  refine r₁.seq ((rel_wp (hinit_rel hH hI fun s s' h => by
        obtain ⟨⟨k, a, -⟩, ⟨k', a', -⟩⟩ := h
        rw [kp_eq hq, scr_eq hq, kl_eq hq, show inn s₀' = inn s₀ from hq.x0.symm,
          show out s₀' = out s₀ from hq.x1.symm] at a'
        exact ⟨a, a', (ke_agree hq k k').1⟩)
      (fun _ h => call_ok hp hz hH hI hId h.1 h.2.1 h.2.2)
      (fun _ h => call_ok hp' hz hH hI hId h.1 h.2.1 h.2.2)).mono (fun _ _ h => h)
    fun _ _ h => ⟨h.1.1, h.2.1⟩)

theorem ct (he : EntryCheck H) (ha : ArgsCheck) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInitAny fun _ _ => True := by
  unfold Hash.hmacInitAny
  obtain ⟨_, hx⟩ := hc.exit
  have ex : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.exit) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x23]) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hx
  exact (entry_rel hp hp' hz hq he).seq ((key_rel hH hp hp' hz hq hc).seq
    (RelCT.assoc ((init_rel hH hp hp' hz hq ha hI hId).seq ex)))

end

/-- `initAny` is verified against `anyG`, given the taint checks and the
proof of HMAC's `init`. -/
theorem verified (hH : HashOK H) (hc : Pbk.Checks H) (he : EntryCheck H) (ha : ArgsCheck)
    (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) (hId : H.hmacInit.aarch64Depth ≤ 1)
    (hsat : ∃ s, (anyG hH.SH (H.W + H.S)).pre s) :
    Verified AArch64.target H.hmacInitAny (anyG hH.SH (H.W + H.S)) := by
  refine ⟨fun s hs => correct (pre_of hH hs) hH.psizes hH hI hId,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH h₁) (pre_of hH h₂) hH.psizes ⟨h1, h2, h3, h4, h5, h6⟩ hc he ha hI hId
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## For each hash function -/

/-- What the kernel checks of `initAny`'s own code (`core H`), once for each
hash function: the taint checks of its entry and of HMAC's `init`'s
arguments. -/
structure AnyOK (C : Hash) : Prop where
  entry : EntryCheck C
  args : ArgsCheck

/-! ## The shared contract -/

/-- `VG.Spec.Hmac.initAnyKeyContract` with its working space (`W` words) as
an argument (as `Proof.Hmac.initScratchContract` is `initContract`'s): the
contract that the function allocating the working space follows from
(`Verified.stackScratchWiped`). -/
def anyScratchContract (S : StreamingHash) (W : Nat) : Contract isa :=
  (Proof.Hmac.initScratchSig S W).contract AArch64.abi
    (post := fun inner outer key keyLen _scratch => Spec.Hmac.initPost S AArch64.abi.ptrBits inner outer key keyLen)
    (writeArgs := true) (stack := 16)

/-- `anyG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem anyImp (S : StreamingHash) (W : Nat) (h : ∃ s, (anyScratchContract S W).pre s) :
    (anyG S W).Implies (anyScratchContract S W) := by
  generic_implies [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, anyG,
    VG.Proof.Pbkdf2.Md.AArch64.Calls.stk, AArch64.abi, AArch64.argRegs] using h

section
variable {H : Hash} (hH : HashOK H) (C : CoreOK (core H)) (A : AnyOK (core H))
include hH C A

/-- `initAny`, verified against the shared contract. -/
theorem hmacInitAny_verified
    (hsI : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W AArch64.abi 16).pre s)
    (hsat : ∃ s, (anyScratchContract hH.SH (H.W + H.S)).pre s) :
    Verified AArch64.target H.hmacInitAny (anyScratchContract hH.SH (H.W + H.S)) :=
  (verified hH (VG.Proof.Pbkdf2.Md.AArch64.Pbk.Checks.of_core C.pbk) A.entry A.args
    (VG.Proof.Pbkdf2.Md.AArch64.hmacInit_ok hH C hsI)
    (VG.Proof.Pbkdf2.Md.AArch64.hmacInit_fdepth hH.stream.initDepth hH.comp.noFrames)
    (anyImp _ _ hsat).sat_left).of_implies (anyImp _ _ hsat)

end

end VG.Proof.Pbkdf2.Md.AArch64.Any
