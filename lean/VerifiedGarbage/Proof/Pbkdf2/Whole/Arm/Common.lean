import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha256
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Impl.Pbkdf2.Whole.Arm
import VerifiedGarbage.Proof.Hmac.Generic.Common

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls`. -/
section

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the calls of HMAC's functions and of `iterate`

As on x86 (`Proof/Pbkdf2/Whole/X86/Calls.lean`): `pbkdf2` calls HMAC's `init`
and `finalize` and PBKDF2's `iterate`, each verified against its shared
contract with 16 bytes of stack; what a caller uses of such a proof is
`Sound`. Each call is in a frame of two words, its stack arguments
(`frame2_ok`, with `WP.callF`, as the callees have frames of their own):
`hi_frame`, `hf_frame` and `it_frame` run one, from the state before its push,
given the registers (`HiArgs`, `HfArgs`, `ItArgs`), which give the callee's
precondition (evaluated with `sig_pre`); `hi_rel`, `hf_rel` and `it_rel`
relate two runs of one. Such a call writes only the 24 bytes below the stack
pointer (`stk`), which `After` lets change; so does a call of a streaming
function, in its frame of 16 bytes (`After.of_hmac`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Arm.FrameStack
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open VG.Proof.Pbkdf2.Stream.Arm (ce0 ce1 ce2 ce3)
open Spec.Sha256 (bytesAt)

/-- What a caller uses of a proof of `Verified Arm.target c k`: that `c`
meets `k` and is constant time under it. -/
structure Sound (c : Prog isa) (k : Contract isa) : Prop where
  ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c

theorem Sound.of_verified {c : Prog isa} {k : Contract isa} (h : Verified Arm.target c k) : VG.Proof.Pbkdf2.Whole.Arm.Sound c k :=
  ⟨h.1, h.2.1⟩

/-- `Sound` for a contract that asks no more and gives no less. -/
theorem Sound.weaken {c : Prog isa} {k k' : Contract isa} (h : VG.Proof.Pbkdf2.Whole.Arm.Sound c k) (hpre : ∀ s, k'.pre s → k.pre s)
    (hpost : ∀ s s', k'.pre s → k.post s s' → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ → k.pub s₁ s₂) : VG.Proof.Pbkdf2.Whole.Arm.Sound c k' :=
  ⟨fun s hs => (h.ok s (hpre s hs)).elim fun t ⟨s', he, ha, hp⟩ => ⟨t, s', he, ha, hpost s s' hs hp⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
      h.ct s₁ s₂ t₁ t₂ s₁' s₂' (hpre _ h₁) (hpre _ h₂) (hpub _ _ h₁ h₂ hp) e₁ e₂⟩

/-! ## The stack below the stack pointer -/

/-- The 24 bytes below the stack pointer, where our frames and calls go. -/
abbrev stk (s : State) : Region := ⟨State.addr s.sp - 24, 24⟩

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and `stk`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [VG.Proof.Pbkdf2.Whole.Arm.stk s]) s.mem s'.mem

theorem stk_eq {s : State} (h : 24 ≤ s.sp.toNat) : belowA s.sp 24 = VG.Proof.Pbkdf2.Whole.Arm.stk s := by
  simp only [belowA, addr_sub' h]; rfl

/-- `n` bytes below the stack pointer are in `stk`. -/
theorem below_stk {s : State} {n : Nat} (hn : n ≤ 24) :
    Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 n, n⟩ (VG.Proof.Pbkdf2.Whole.Arm.stk s) :=
  fun x hx => Offset.below_mono _ (a := n) (b := 24) hn (by decide) x hx

/-- A call of a streaming function in its frame (`Proof/Pbkdf2/Stream/Arm/Hash.lean`). -/
theorem After.of_hmac {s s' : State} {ws : List Region}
    (h : Pbkdf2.Stream.Arm.After s ws s') : VG.Proof.Pbkdf2.Whole.Arm.After s ws s' :=
  ⟨h.rd, h.wr, h.sp, h.cs, Frame.sub h.frame fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), VG.Proof.Pbkdf2.Whole.Arm.below_stk (s := s) (n := 16) (by decide)⟩⟩

/-- Two ranges below `p` that do not overlap. -/
theorem bdisj (p : Addr) (c : Nat) {a n b k : Nat} (ha : a ≤ c) (hb : b ≤ c)
    (h : c - a + n ≤ c - b ∨ c - b + k ≤ c - a) (hn : c + n < 2 ^ 32) (hk : c + k < 2 ^ 32) :
    Region.Disjoint ⟨p - BitVec.ofNat 64 a, n⟩ ⟨p - BitVec.ofNat 64 b, k⟩ := by
  rw [Offset.sub_ofNat_eq p ha, Offset.sub_ofNat_eq p hb]
  exact Offset.disjoint _ h (by omega) (by omega)

/-! ## A frame of two words around a call -/

section Frame2
variable {ra rb : Reg} {s : State}

theorem p2_mem :
    (pushed [ra, rb] s).mem = (s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 8)) (s.gpr ra)).writeW
      (State.addr (s.sp - BitVec.ofNat 32 8 + 4)) (s.gpr rb) := rfl

theorem p2_sp : (pushed [ra, rb] s).sp = s.sp - BitVec.ofNat 32 8 := rfl

theorem a8 (h : 8 ≤ s.sp.toNat) : State.addr (s.sp - BitVec.ofNat 32 8) = State.addr s.sp - BitVec.ofNat 64 8 :=
  addr_sub' h

theorem a84 (h : 8 ≤ s.sp.toNat) :
    State.addr (s.sp - BitVec.ofNat 32 8 + 4) = State.addr s.sp - BitVec.ofNat 64 8 + BitVec.ofNat 64 4 := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, addr_add (by rw [sub_toNat' h]; have := s.sp.isLt; omega),
    VG.Proof.Pbkdf2.Whole.Arm.a8 h]

theorem p2_arg0 (h : 8 ≤ s.sp.toNat) {rd wr : List Region} :
    VG.Arm.stackArg ((pushed [ra, rb] s).callEntry.withRegions rd wr) 0 = s.gpr ra := by
  simp only [VG.Arm.stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, VG.Proof.Pbkdf2.Whole.Arm.p2_sp, Nat.mul_zero]
  rw [VG.Proof.Pbkdf2.Whole.Arm.p2_mem, BitVec.add_zero, VG.Proof.Pbkdf2.Whole.Arm.a84 h, VG.Proof.Pbkdf2.Whole.Arm.a8 h,
    Mem.readW_writeW_sep (Pbkdf2.Stream.Arm.sep_base_off _ (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem p2_arg1 {rd wr : List Region} :
    VG.Arm.stackArg ((pushed [ra, rb] s).callEntry.withRegions rd wr) 1 = s.gpr rb := by
  simp only [VG.Arm.stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, VG.Proof.Pbkdf2.Whole.Arm.p2_sp, Nat.mul_one]
  rw [VG.Proof.Pbkdf2.Whole.Arm.p2_mem, show BitVec.ofNat 32 4 = (4 : BitVec 32) from rfl, Mem.readW_writeW_self32]

theorem p2_argAddr {rd wr : List Region} :
    stackArgAddr ((pushed [ra, rb] s).callEntry.withRegions rd wr) 0 = State.addr (s.sp - BitVec.ofNat 32 8) := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Whole.Arm.p2_sp, Nat.mul_zero]
  rw [BitVec.add_zero]

omit ra rb in
/-- The frame's 8 bytes are in `stk`. -/
theorem p2_sub (h : 24 ≤ s.sp.toNat) : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ (VG.Proof.Pbkdf2.Whole.Arm.stk s) := by
  rw [VG.Proof.Pbkdf2.Whole.Arm.a8 (by omega)]; exact VG.Proof.Pbkdf2.Whole.Arm.below_stk (by decide)

omit ra rb in
/-- The callee's 16 bytes below its stack pointer are in `stk`. -/
theorem p2_csub (h : 24 ≤ s.sp.toNat) :
    Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8) - 16, 16⟩ (VG.Proof.Pbkdf2.Whole.Arm.stk s) := by
  rw [VG.Proof.Pbkdf2.Whole.Arm.a8 (by omega), BitVec.sub_sub, show BitVec.ofNat 64 8 + 16 = BitVec.ofNat 64 24 from rfl]
  exact Region.sub_prefix (by decide)

omit ra rb in
/-- And they are apart from the frame. -/
theorem p2_cdisj (h : 24 ≤ s.sp.toNat) {n : Nat} (hn : n ≤ 8) :
    Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 8) - 16, 16⟩ ⟨State.addr (s.sp - BitVec.ofNat 32 8), n⟩ := by
  rw [VG.Proof.Pbkdf2.Whole.Arm.a8 (by omega), BitVec.sub_sub, show BitVec.ofNat 64 8 + 16 = BitVec.ofNat 64 24 from rfl]
  exact VG.Proof.Pbkdf2.Whole.Arm.bdisj _ 24 (a := 24) (b := 8) (by decide) (by decide) (by omega) (by decide) (by omega)

end Frame2

/-- A frame of two words, popped into `t`, around a call of verified code
that uses at most 16 bytes of stack: the callee runs from the state after
the push, and the frame leaves `After`. -/
theorem frame2_ok {ra rb t : Reg} (hrs : regList [ra, rb] = true) (ht : t ∉ preserved)
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hst : armStack c ≤ 16) {s : State} (h24 : 24 ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed [ra, rb] s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr))
    (hw : Covers wr (pushed [ra, rb] s).wr) {Q : State → Prop}
    (hQ : ∀ s₂ : State, VG.Proof.Pbkdf2.Whole.Arm.After s wr (popped t 8 s₂) →
      k.post ((pushed [ra, rb] s).callEntry.withRegions rd wr) (s₂.withRegions rd wr) → Q (popped t 8 s₂)) :
    WP isa (.frame (.push [ra, rb]) (.call n c) (.pop t 8)) s Q := by
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega)
  refine WP.frame (rs := [ra, rb]) (r := t) hrs (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine WP.callF hv hpre hc hw (by rw [VG.Proof.Pbkdf2.Whole.Arm.p2_sp, h8]; omega) fun s₂ hrd hwr hsp hf hcs hpost => ?_
  refine hQ s₂ ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ hpost
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, VG.Proof.Pbkdf2.Whole.Arm.p2_sp]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ t := fun e => ht (e ▸ hr)
    rw [popped_gpr this, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    have f₀ := pushed_frameA (rs := [ra, rb]) (s := s) (by simp only [List.length_cons, List.length_nil]; omega)
    refine Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), VG.Proof.Pbkdf2.Whole.Arm.p2_sub h24⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [VG.Proof.Pbkdf2.Whole.Arm.p2_sp, ← VG.Proof.Pbkdf2.Whole.Arm.stk_eq h24]
        exact belowA_inner (k := 8) (by omega) h24

/-- Two runs of such a frame leak the same, if their stack pointers are the
same and the callee's preconditions and public data hold. -/
theorem frame2_rel {ra rb t : Reg} (hrs : regList [ra, rb] = true) {n : String} {c : Prog isa}
    {k : Contract isa} (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧
      k.pre ((pushed [ra, rb] s₁).callEntry.withRegions rd wr) ∧
      k.pre ((pushed [ra, rb] s₂).callEntry.withRegions rd wr) ∧
      k.pub ((pushed [ra, rb] s₁).callEntry.withRegions rd wr) ((pushed [ra, rb] s₂).callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) ((pushed [ra, rb] s₁).rd ++ (pushed [ra, rb] s₁).wr) ∧ Covers wr (pushed [ra, rb] s₁).wr ∧
      Covers (rd ++ wr) ((pushed [ra, rb] s₂).rd ++ (pushed [ra, rb] s₂).wr) ∧ Covers wr (pushed [ra, rb] s₂).wr) :
    RelCT isa P (.frame (.push [ra, rb]) (.call n c) (.pop t 8)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h s₁ s₂ hp).1) (RelCT.call hv hct rd wr fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_)
  rw [Pbkdf2.Stream.Arm.push_eq hrs pa, Pbkdf2.Stream.Arm.push_eq hrs pb]
  exact (h s₁ s₂ hp).2

/-- The representation of a streaming state depends only on its bytes. -/
def ReprOK (S : StreamingHash) : Prop :=
  ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < S.stateBytes, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) → S.Repr m p msg → S.Repr m' q msg

/-- The memory on entry to a callee in a frame of two words is ours outside `stk`. -/
theorem p2_frame {ra rb : Reg} {s : State} (h24 : 24 ≤ s.sp.toNat) :
    Frame [VG.Proof.Pbkdf2.Whole.Arm.stk s] s.mem (pushed [ra, rb] s).mem :=
  Frame.sub (pushed_frameA (rs := [ra, rb]) (s := s) (by simp only [List.length_cons, List.length_nil]; omega))
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, VG.Proof.Pbkdf2.Whole.Arm.p2_sub h24⟩

theorem p2_bytes {ra rb : Reg} {s : State} (h24 : 24 ≤ s.sp.toNat) {p : Addr} {k : Nat}
    (hd : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨p, k⟩) (hk : k ≤ 2 ^ 64) :
    bytesAt (pushed [ra, rb] s).mem p k = bytesAt s.mem p k := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => (VG.Proof.Pbkdf2.Whole.Arm.p2_frame h24).bytes (R := ⟨p, k⟩)
    (by simp only [List.mem_singleton]; rintro q rfl; exact hd.symm) hk (List.mem_range.mp hi)

theorem p2_repr {S : StreamingHash} (hR : VG.Proof.Pbkdf2.Whole.Arm.ReprOK S) (hS : S.stateBytes ≤ 2 ^ 64) {ra rb : Reg} {s : State}
    (h24 : 24 ≤ s.sp.toNat) {p : Addr} (hd : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨p, S.stateBytes⟩) {msg : List Byte}
    (h : S.Repr s.mem p msg) : S.Repr (pushed [ra, rb] s).mem p msg :=
  hR _ _ _ _ _ (fun i hi => (VG.Proof.Pbkdf2.Whole.Arm.p2_frame h24).bytes (R := ⟨p, S.stateBytes⟩)
    (by simp only [List.mem_singleton]; rintro q rfl; exact hd.symm) hS hi) h

/-! ## HMAC's `init`, in a frame of `scratch` -/

/-- What a framed call of HMAC's `init` needs of the state before its push:
the states at `inn` and `out` in `r0` and `r1`, the `kl` bytes of key at `k`
in `r2` and `r3`, and `8 Wi` bytes of scratch space at `sc` in `r12`; the
regions the callee may read and write; that they are disjoint as it needs,
and from the 24 bytes below the stack pointer; and that none of them wraps
around. -/
structure HiArgs (S : StreamingHash) (Wi : Nat) (s : State) (inn out k sc : BitVec 32) (kl : Nat) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = out
  r2 : s.gpr .r2 = k
  r3 : s.gpr .r3 = BitVec.ofNat 32 kl
  r12 : s.gpr .r12 = sc
  klB : kl ≤ S.H.blockSize
  kl32 : kl < 2 ^ 32
  sp : 24 ≤ s.sp.toNat
  cr : Covers [⟨State.addr k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr out, S.stateBytes⟩, ⟨State.addr sc, Wi * 8⟩] s.wr
  i_o : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr out, S.stateBytes⟩
  i_k : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr k, kl⟩
  i_s : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr sc, Wi * 8⟩
  o_k : Region.Disjoint ⟨State.addr out, S.stateBytes⟩ ⟨State.addr k, kl⟩
  o_s : Region.Disjoint ⟨State.addr out, S.stateBytes⟩ ⟨State.addr sc, Wi * 8⟩
  k_s : Region.Disjoint ⟨State.addr k, kl⟩ ⟨State.addr sc, Wi * 8⟩
  b_i : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr inn, S.stateBytes⟩
  b_o : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr out, S.stateBytes⟩
  b_k : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr k, kl⟩
  b_s : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr sc, Wi * 8⟩
  ni : inn.toNat + S.stateBytes ≤ 2 ^ 32
  no : out.toNat + S.stateBytes ≤ 2 ^ 32
  nk : k.toNat + kl ≤ 2 ^ 32
  nsc : sc.toNat + Wi * 8 ≤ 2 ^ 32

/-- The frame of HMAC's `init` and of `iterate`. -/
abbrev fr1 : List Reg := [.r12, .lr]

/-- The regions `init` is given. -/
abbrev HiArgs.rd (sp k : BitVec 32) (kl : Nat) : List Region :=
  [⟨State.addr k, kl⟩, ⟨State.addr (sp - BitVec.ofNat 32 8), 4⟩]
abbrev HiArgs.wr (S : StreamingHash) (Wi : Nat) (inn out sc : BitVec 32) : List Region :=
  [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr out, S.stateBytes⟩, ⟨State.addr sc, Wi * 8⟩]

namespace HiArgs
variable {S : StreamingHash} {Wi : Nat} {s : State} {inn out k sc : BitVec 32} {kl : Nat}
  (h : VG.Proof.Pbkdf2.Whole.Arm.HiArgs S Wi s inn out k sc kl)
include h

/-- `init`'s precondition on entry. -/
theorem pre : (Spec.Hmac.initScratchContract S Wi Arm.abi 16).pre
    ((pushed VG.Proof.Pbkdf2.Whole.Arm.fr1 s).callEntry.withRegions (HiArgs.rd s.sp k kl) (HiArgs.wr S Wi inn out sc)) := by
  have e := h.sp
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega)
  have sA := VG.Proof.Pbkdf2.Whole.Arm.p2_sub (s := s) e
  have sR := VG.Proof.Pbkdf2.Whole.Arm.p2_csub (s := s) e
  have cA := VG.Proof.Pbkdf2.Whole.Arm.p2_cdisj (s := s) e (n := 4) (by decide)
  have sA4 : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 4⟩ (VG.Proof.Pbkdf2.Whole.Arm.stk s) := fun x hx => sA x (Region.sub_prefix (by decide) x hx)
  sig_pre [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [h.r0, h.r1, h.r2, h.r3, VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s) (by omega), VG.Proof.Pbkdf2.Whole.Arm.p2_argAddr, h.r12, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h.kl32]
  exact ⟨by rw [h8]; omega, by rw [h8]; have := s.sp.isLt; omega, rfl, rfl, h.i_o, h.i_k, h.i_s,
    (h.b_i.sub_left sA4).symm, h.o_k, h.o_s, (h.b_o.sub_left sA4).symm, h.k_s, (h.b_s.sub_left sA4).symm,
    h.b_i.sub_left sR, h.b_o.sub_left sR, h.b_k.sub_left sR, h.b_s.sub_left sR, cA,
    h.ni, h.no, h.nk, h.nsc, h.klB⟩

theorem cov : Covers (HiArgs.rd s.sp k kl ++ HiArgs.wr S Wi inn out sc) ((pushed VG.Proof.Pbkdf2.Whole.Arm.fr1 s).rd ++ (pushed VG.Proof.Pbkdf2.Whole.Arm.fr1 s).wr) := by
  intro a n ⟨q, hq, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [pushed_rd, pushed_wr]
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_singleton_self _, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · refine ⟨_, List.mem_append_right _ List.mem_cons_self, ?_⟩
    show Region.Contains ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ a n
    simp only [Region.Contains] at hc ⊢; omega
  all_goals
    obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
    exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩

theorem covW : Covers (HiArgs.wr S Wi inn out sc) (pushed VG.Proof.Pbkdf2.Whole.Arm.fr1 s).wr := by
  intro a n hi
  obtain ⟨q', hq', hc'⟩ := h.cw a n hi
  exact ⟨q', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hq', hc'⟩

end HiArgs

theorem hi_frame {S : StreamingHash} {Wi : Nat} {n : String} {c : Prog isa}
    (hv : VG.Proof.Pbkdf2.Whole.Arm.Sound c (Spec.Hmac.initScratchContract S Wi Arm.abi 16)) (hst : armStack c ≤ 16)
    {s : State} {inn out k sc : BitVec 32} {kl : Nat} (h : VG.Proof.Pbkdf2.Whole.Arm.HiArgs S Wi s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Whole.Arm.After s (HiArgs.wr S Wi inn out sc) s' →
      S.Repr s'.mem (State.addr inn) (xorPad (blockKey S.H (bytesAt s.mem (State.addr k) kl)) ipad) →
      S.Repr s'.mem (State.addr out) (xorPad (blockKey S.H (bytesAt s.mem (State.addr k) kl)) opad) → Q s') :
    WP isa (.frame (.push VG.Proof.Pbkdf2.Whole.Arm.fr1) (.call n c) (.pop .r12 8)) s Q := by
  refine VG.Proof.Pbkdf2.Whole.Arm.frame2_ok rfl (by decide) hv.ok hst h.sp h.pre h.cov h.covW fun s₂ a post => ?_
  sig_post [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at post
  simp only [
    h.r0, h.r1, h.r2, h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.kl32] at post
  have ek : bytesAt (storeWords s.mem (s.sp - BitVec.ofNat 32 8) [s.gpr .r12, s.gpr .lr]) (BitVec.setWidth 64 k) kl =
      bytesAt s.mem (State.addr k) kl :=
    VG.Proof.Pbkdf2.Whole.Arm.p2_bytes (ra := .r12) (rb := .lr) h.sp h.b_k (by have := h.kl32; omega)
  rw [ek] at post
  exact hQ _ a (by rw [popped_mem]; exact post.1) (by rw [popped_mem]; exact post.2)

theorem hi_rel {S : StreamingHash} {Wi : Nat} {n : String} {c : Prog isa}
    (hv : VG.Proof.Pbkdf2.Whole.Arm.Sound c (Spec.Hmac.initScratchContract S Wi Arm.abi 16)) {P : State → State → Prop}
    {sp inn out k sc : BitVec 32} {kl : Nat}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Whole.Arm.HiArgs S Wi s inn out k sc kl ∧ VG.Proof.Pbkdf2.Whole.Arm.HiArgs S Wi s' inn out k sc kl ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push VG.Proof.Pbkdf2.Whole.Arm.fr1) (.call n c) (.pop .r12 8)) fun _ _ => True := by
  refine VG.Proof.Pbkdf2.Whole.Arm.frame2_rel rfl hv.ok hv.ct (HiArgs.rd sp k kl) (HiArgs.wr S Wi inn out sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.pre; have c' := a'.pre
  rw [e] at c; rw [e'] at c'
  have v := a.cov; have v' := a'.cov
  rw [e] at v; rw [e'] at v'
  refine ⟨e.trans e'.symm, c, c', ?_, v, a.covW, v', a'.covW⟩
  sig_pub [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [
    a.r0, a'.r0, a.r1, a'.r1, a.r2, a'.r2, a.r3, a'.r3, VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s) (by have := a.sp; omega),
    VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s') (by have := a'.sp; omega), a.r12, a'.r12, e, e', and_self]

/-! ## HMAC's `finalize`, in a frame of `out` and `scratch` -/

/-- What a framed call of HMAC's `finalize` needs of the state before its
push: the inner and outer states at `inn` and `ou` in `r0` and `r1`, the
count in `r3:r2`, `out` at `o` in `r10` and `8 Wf` bytes of scratch space
at `sc` in `r12`, as for `init`. -/
structure HfArgs (S : StreamingHash) (Wf : Nat) (s : State) (inn ou o sc : BitVec 32) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = ou
  r10 : s.gpr .r10 = o
  r12 : s.gpr .r12 = sc
  sp : 24 ≤ s.sp.toNat
  cr : Covers [⟨State.addr ou, S.stateBytes⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr o, S.digestBytes⟩, ⟨State.addr sc, Wf * 8⟩] s.wr
  i_u : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr ou, S.stateBytes⟩
  i_o : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr o, S.digestBytes⟩
  i_s : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr sc, Wf * 8⟩
  u_o : Region.Disjoint ⟨State.addr ou, S.stateBytes⟩ ⟨State.addr o, S.digestBytes⟩
  u_s : Region.Disjoint ⟨State.addr ou, S.stateBytes⟩ ⟨State.addr sc, Wf * 8⟩
  o_s : Region.Disjoint ⟨State.addr o, S.digestBytes⟩ ⟨State.addr sc, Wf * 8⟩
  b_i : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr inn, S.stateBytes⟩
  b_u : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr ou, S.stateBytes⟩
  b_o : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr o, S.digestBytes⟩
  b_s : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr sc, Wf * 8⟩
  ni : inn.toNat + S.stateBytes ≤ 2 ^ 32
  nu : ou.toNat + S.stateBytes ≤ 2 ^ 32
  no : o.toNat + S.digestBytes ≤ 2 ^ 32
  nsc : sc.toNat + Wf * 8 ≤ 2 ^ 32

/-- The frame of HMAC's `finalize`. -/
abbrev fr2 : List Reg := [.r10, .r12]

/-- The regions `finalize` is given. -/
abbrev HfArgs.rd (S : StreamingHash) (sp ou : BitVec 32) : List Region :=
  [⟨State.addr ou, S.stateBytes⟩, ⟨State.addr (sp - BitVec.ofNat 32 8), 8⟩]
abbrev HfArgs.wr (S : StreamingHash) (Wf : Nat) (inn o sc : BitVec 32) : List Region :=
  [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr o, S.digestBytes⟩, ⟨State.addr sc, Wf * 8⟩]

namespace HfArgs
variable {S : StreamingHash} {Wf : Nat} {s : State} {inn ou o sc : BitVec 32}
  (h : VG.Proof.Pbkdf2.Whole.Arm.HfArgs S Wf s inn ou o sc)
include h

theorem pre : (Spec.Hmac.finalizeScratchContract S Wf Arm.abi 16).pre
    ((pushed VG.Proof.Pbkdf2.Whole.Arm.fr2 s).callEntry.withRegions (HfArgs.rd S s.sp ou) (HfArgs.wr S Wf inn o sc)) := by
  have e := h.sp
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega)
  have sA := VG.Proof.Pbkdf2.Whole.Arm.p2_sub (s := s) e
  have sR := VG.Proof.Pbkdf2.Whole.Arm.p2_csub (s := s) e
  have cA := VG.Proof.Pbkdf2.Whole.Arm.p2_cdisj (s := s) e (n := 8) (by decide)
  sig_pre [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [h.r0, h.r1, VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s) (by omega), VG.Proof.Pbkdf2.Whole.Arm.p2_arg1, VG.Proof.Pbkdf2.Whole.Arm.p2_argAddr, h.r10, h.r12]
  exact ⟨by rw [h8]; omega, by rw [h8]; have := s.sp.isLt; omega, rfl, rfl, h.i_u, h.i_o, h.i_s,
    (h.b_i.sub_left sA).symm, h.u_o, h.u_s, h.o_s, (h.b_o.sub_left sA).symm, (h.b_s.sub_left sA).symm,
    h.b_i.sub_left sR, h.b_u.sub_left sR, h.b_o.sub_left sR, h.b_s.sub_left sR, cA,
    h.ni, h.nu, h.no, h.nsc⟩

theorem cov : Covers (HfArgs.rd S s.sp ou ++ HfArgs.wr S Wf inn o sc) ((pushed VG.Proof.Pbkdf2.Whole.Arm.fr2 s).rd ++ (pushed VG.Proof.Pbkdf2.Whole.Arm.fr2 s).wr) := by
  intro a n ⟨q, hq, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [pushed_rd, pushed_wr]
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_singleton_self _, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · exact ⟨_, List.mem_append_right _ List.mem_cons_self, hc⟩
  all_goals
    obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
    exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩

theorem covW : Covers (HfArgs.wr S Wf inn o sc) (pushed VG.Proof.Pbkdf2.Whole.Arm.fr2 s).wr := by
  intro a n hi
  obtain ⟨q', hq', hc'⟩ := h.cw a n hi
  exact ⟨q', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hq', hc'⟩

end HfArgs

theorem hf_frame {S : StreamingHash} {Wf : Nat} {n : String} {c : Prog isa} (hR : VG.Proof.Pbkdf2.Whole.Arm.ReprOK S)
    (hSn : S.stateBytes ≤ 2 ^ 64) (hv : VG.Proof.Pbkdf2.Whole.Arm.Sound c (Spec.Hmac.finalizeScratchContract S Wf Arm.abi 16))
    (hst : armStack c ≤ 16) {s : State} {inn ou o sc : BitVec 32} (h : VG.Proof.Pbkdf2.Whole.Arm.HfArgs S Wf s inn ou o sc)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Whole.Arm.After s (HfArgs.wr S Wf inn o sc) s' →
      (∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
        S.Repr s.mem (State.addr inn) (xorPad k0 ipad ++ text) →
        s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 (S.H.blockSize + text.length) →
        S.Repr s.mem (State.addr ou) (xorPad k0 opad) →
        bytesAt s'.mem (State.addr o) S.digestBytes = hmacBlockKey S.H k0 text) → Q s') :
    WP isa (.frame (.push VG.Proof.Pbkdf2.Whole.Arm.fr2) (.call n c) (.pop .r12 8)) s Q := by
  refine VG.Proof.Pbkdf2.Whole.Arm.frame2_ok rfl (by decide) hv.ok hst h.sp h.pre h.cov h.covW fun s₂ a post => ?_
  sig_post [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at post
  simp only [h.r0, h.r1, VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s) (by have := h.sp; omega)] at post
  refine hQ _ a fun k0 text hk hl hi hc ho => ?_
  rw [popped_mem, ← h.r10]
  exact post k0 text hk hl (VG.Proof.Pbkdf2.Whole.Arm.p2_repr (ra := .r10) (rb := .r12) hR hSn h.sp h.b_i hi) hc
    (VG.Proof.Pbkdf2.Whole.Arm.p2_repr (ra := .r10) (rb := .r12) hR hSn h.sp h.b_u ho)

theorem hf_rel {S : StreamingHash} {Wf : Nat} {n : String} {c : Prog isa}
    (hv : VG.Proof.Pbkdf2.Whole.Arm.Sound c (Spec.Hmac.finalizeScratchContract S Wf Arm.abi 16)) {P : State → State → Prop}
    {sp inn ou o sc : BitVec 32}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Whole.Arm.HfArgs S Wf s inn ou o sc ∧ VG.Proof.Pbkdf2.Whole.Arm.HfArgs S Wf s' inn ou o sc ∧
      s.gpr .r2 = s'.gpr .r2 ∧ s.gpr .r3 = s'.gpr .r3 ∧ s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push VG.Proof.Pbkdf2.Whole.Arm.fr2) (.call n c) (.pop .r12 8)) fun _ _ => True := by
  refine VG.Proof.Pbkdf2.Whole.Arm.frame2_rel rfl hv.ok hv.ct (HfArgs.rd S sp ou) (HfArgs.wr S Wf inn o sc) fun s s' hp => ?_
  obtain ⟨a, a', c2, c3, e, e'⟩ := h s s' hp
  have c := a.pre; have c' := a'.pre
  rw [e] at c; rw [e'] at c'
  have v := a.cov; have v' := a'.cov
  rw [e] at v; rw [e'] at v'
  refine ⟨e.trans e'.symm, c, c', ?_, v, a.covW, v', a'.covW⟩
  sig_pub [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [
    a.r0, a'.r0, a.r1, a'.r1, c2, c3, VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s) (by have := a.sp; omega),
    VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s') (by have := a'.sp; omega), VG.Proof.Pbkdf2.Whole.Arm.p2_arg1,
    VG.Proof.Pbkdf2.Whole.Arm.p2_arg1 (s := s'), a.r10, a'.r10, a.r12, a'.r12, e, e', and_self]

/-! ## `iterate`, in a frame of `scratch` -/

/-- What a framed call of `iterate` needs of the state before its push: the
key's states at `key` in `r0`, `U` at `u` in `r1`, `n` in `r2`, `T` at `tt`
in `r3` and `8 Wt` bytes of scratch space at `sc` in `r12`, as for `init`. -/
structure ItArgs (S : StreamingHash) (Wt : Nat) (s : State) (key u n tt sc : BitVec 32) : Prop where
  r0 : s.gpr .r0 = key
  r1 : s.gpr .r1 = u
  r2 : s.gpr .r2 = n
  r3 : s.gpr .r3 = tt
  r12 : s.gpr .r12 = sc
  sp : 24 ≤ s.sp.toNat
  cr : Covers [⟨State.addr key, 2 * S.stateBytes⟩, ⟨State.addr u, S.digestBytes⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr tt, S.digestBytes⟩, ⟨State.addr sc, Wt * 8⟩] s.wr
  k_t : Region.Disjoint ⟨State.addr key, 2 * S.stateBytes⟩ ⟨State.addr tt, S.digestBytes⟩
  k_s : Region.Disjoint ⟨State.addr key, 2 * S.stateBytes⟩ ⟨State.addr sc, Wt * 8⟩
  u_t : Region.Disjoint ⟨State.addr u, S.digestBytes⟩ ⟨State.addr tt, S.digestBytes⟩
  u_s : Region.Disjoint ⟨State.addr u, S.digestBytes⟩ ⟨State.addr sc, Wt * 8⟩
  t_s : Region.Disjoint ⟨State.addr tt, S.digestBytes⟩ ⟨State.addr sc, Wt * 8⟩
  b_k : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr key, 2 * S.stateBytes⟩
  b_u : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr u, S.digestBytes⟩
  b_t : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr tt, S.digestBytes⟩
  b_s : (VG.Proof.Pbkdf2.Whole.Arm.stk s).Disjoint ⟨State.addr sc, Wt * 8⟩
  nk : key.toNat + 2 * S.stateBytes ≤ 2 ^ 32
  nu : u.toNat + S.digestBytes ≤ 2 ^ 32
  nt : tt.toNat + S.digestBytes ≤ 2 ^ 32
  nsc : sc.toNat + Wt * 8 ≤ 2 ^ 32

/-- The regions `iterate` is given. -/
abbrev ItArgs.rd (S : StreamingHash) (sp key u : BitVec 32) : List Region :=
  [⟨State.addr key, 2 * S.stateBytes⟩, ⟨State.addr u, S.digestBytes⟩, ⟨State.addr (sp - BitVec.ofNat 32 8), 4⟩]
abbrev ItArgs.wr (S : StreamingHash) (Wt : Nat) (tt sc : BitVec 32) : List Region :=
  [⟨State.addr tt, S.digestBytes⟩, ⟨State.addr sc, Wt * 8⟩]

namespace ItArgs
variable {S : StreamingHash} {Wt : Nat} {s : State} {key u n tt sc : BitVec 32}
  (h : VG.Proof.Pbkdf2.Whole.Arm.ItArgs S Wt s key u n tt sc)
include h

theorem pre : (Spec.Pbkdf2.iterateContract S Wt Arm.abi 16).pre
    ((pushed VG.Proof.Pbkdf2.Whole.Arm.fr1 s).callEntry.withRegions (ItArgs.rd S s.sp key u) (ItArgs.wr S Wt tt sc)) := by
  have e := h.sp
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega)
  have sA := VG.Proof.Pbkdf2.Whole.Arm.p2_sub (s := s) e
  have sR := VG.Proof.Pbkdf2.Whole.Arm.p2_csub (s := s) e
  have cA := VG.Proof.Pbkdf2.Whole.Arm.p2_cdisj (s := s) e (n := 4) (by decide)
  have sA4 : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 4⟩ (VG.Proof.Pbkdf2.Whole.Arm.stk s) := fun x hx => sA x (Region.sub_prefix (by decide) x hx)
  sig_pre [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [h.r0, h.r1, h.r3, VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s) (by omega), VG.Proof.Pbkdf2.Whole.Arm.p2_argAddr, h.r12]
  exact ⟨by rw [h8]; omega, by rw [h8]; have := s.sp.isLt; omega, rfl, rfl, h.k_t, h.k_s, h.u_t, h.u_s,
    h.t_s, (h.b_t.sub_left sA4).symm, (h.b_s.sub_left sA4).symm,
    h.b_k.sub_left sR, h.b_u.sub_left sR, h.b_t.sub_left sR, h.b_s.sub_left sR, cA,
    h.nk, h.nu, h.nt, h.nsc⟩

theorem cov : Covers (ItArgs.rd S s.sp key u ++ ItArgs.wr S Wt tt sc) ((pushed VG.Proof.Pbkdf2.Whole.Arm.fr1 s).rd ++ (pushed VG.Proof.Pbkdf2.Whole.Arm.fr1 s).wr) := by
  intro a n ⟨q, hq, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [pushed_rd, pushed_wr]
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_cons_self, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · refine ⟨_, List.mem_append_right _ List.mem_cons_self, ?_⟩
    show Region.Contains ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ a n
    simp only [Region.Contains] at hc ⊢; omega
  all_goals
    obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
    exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩

theorem covW : Covers (ItArgs.wr S Wt tt sc) (pushed VG.Proof.Pbkdf2.Whole.Arm.fr1 s).wr := by
  intro a n hi
  obtain ⟨q', hq', hc'⟩ := h.cw a n hi
  exact ⟨q', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hq', hc'⟩

end ItArgs

theorem it_frame {S : StreamingHash} {Wt : Nat} {nm : String} {c : Prog isa} (hR : VG.Proof.Pbkdf2.Whole.Arm.ReprOK S)
    (hSn : 2 * S.stateBytes ≤ 2 ^ 32) (hDn : S.digestBytes ≤ 2 ^ 32)
    (hv : VG.Proof.Pbkdf2.Whole.Arm.Sound c (Spec.Pbkdf2.iterateContract S Wt Arm.abi 16)) (hst : armStack c ≤ 16)
    {s : State} {key u n tt sc : BitVec 32} (h : VG.Proof.Pbkdf2.Whole.Arm.ItArgs S Wt s key u n tt sc) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Whole.Arm.After s (ItArgs.wr S Wt tt sc) s' →
      (∀ k0, k0.length = S.H.blockSize → S.Repr s.mem (State.addr key) (xorPad k0 ipad) →
        S.Repr s.mem (State.addr key + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
        bytesAt s'.mem (State.addr tt) S.digestBytes =
          Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) n.toNat (bytesAt s.mem (State.addr u) S.digestBytes)
            (bytesAt s.mem (State.addr tt) S.digestBytes)) → Q s') :
    WP isa (.frame (.push VG.Proof.Pbkdf2.Whole.Arm.fr1) (.call nm c) (.pop .r12 8)) s Q := by
  refine VG.Proof.Pbkdf2.Whole.Arm.frame2_ok rfl (by decide) hv.ok hst h.sp h.pre h.cov h.covW fun s₂ a post => ?_
  sig_post [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at post
  simp only [h.r0, h.r1, h.r2, h.r3] at post
  refine hQ _ a fun k0 hk hi ho => ?_
  rw [popped_mem]
  have := post k0 hk
    (VG.Proof.Pbkdf2.Whole.Arm.p2_repr (ra := .r12) (rb := .lr) (p := State.addr key) hR (by omega) h.sp
      (h.b_k.sub_right (Region.sub_prefix (by omega))) hi)
    (VG.Proof.Pbkdf2.Whole.Arm.p2_repr (ra := .r12) (rb := .lr) (p := State.addr key + BitVec.ofNat 64 S.stateBytes) hR (by omega) h.sp
      (h.b_k.sub_right (Offset.sub_base _ (by omega))) ho)
  have eu : bytesAt (storeWords s.mem (s.sp - BitVec.ofNat 32 8) [s.gpr .r12, s.gpr .lr]) (BitVec.setWidth 64 u)
      S.digestBytes = bytesAt s.mem (State.addr u) S.digestBytes :=
    VG.Proof.Pbkdf2.Whole.Arm.p2_bytes (ra := .r12) (rb := .lr) h.sp h.b_u (by omega)
  have et : bytesAt (storeWords s.mem (s.sp - BitVec.ofNat 32 8) [s.gpr .r12, s.gpr .lr]) (BitVec.setWidth 64 tt)
      S.digestBytes = bytesAt s.mem (State.addr tt) S.digestBytes :=
    VG.Proof.Pbkdf2.Whole.Arm.p2_bytes (ra := .r12) (rb := .lr) h.sp h.b_t (by omega)
  rw [eu, et] at this
  exact this

theorem it_rel {S : StreamingHash} {Wt : Nat} {nm : String} {c : Prog isa}
    (hv : VG.Proof.Pbkdf2.Whole.Arm.Sound c (Spec.Pbkdf2.iterateContract S Wt Arm.abi 16)) {P : State → State → Prop}
    {sp key u n tt sc : BitVec 32}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Whole.Arm.ItArgs S Wt s key u n tt sc ∧ VG.Proof.Pbkdf2.Whole.Arm.ItArgs S Wt s' key u n tt sc ∧ s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push VG.Proof.Pbkdf2.Whole.Arm.fr1) (.call nm c) (.pop .r12 8)) fun _ _ => True := by
  refine VG.Proof.Pbkdf2.Whole.Arm.frame2_rel rfl hv.ok hv.ct (ItArgs.rd S sp key u) (ItArgs.wr S Wt tt sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.pre; have c' := a'.pre
  rw [e] at c; rw [e'] at c'
  have v := a.cov; have v' := a'.cov
  rw [e] at v; rw [e'] at v'
  refine ⟨e.trans e'.symm, c, c', ?_, v, a.covW, v', a'.covW⟩
  sig_pub [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [
    a.r0, a'.r0, a.r1, a'.r1, a.r2, a'.r2, a.r3, a'.r3, VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s) (by have := a.sp; omega),
    VG.Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s') (by have := a'.sp; omega), a.r12, a'.r12, e, e', and_self]

end VG.Proof.Pbkdf2.Whole.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common`. -/
section

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the functions it calls, and its parts

As on x86 (`Proof/Pbkdf2/Whole/X86/Common.lean`): `FnsOK F` is what the proof
knows of the functions `pbkdf2` calls (the hash function's streaming
functions, `VG.Proof.Pbkdf2.Stream.Arm.HashOK`, and HMAC's `init` and
`finalize` and PBKDF2's `iterate`, sound for their shared contracts with 16
bytes of stack). Then the precondition of `pbkdf2` (`Pre`, from the shared
contract with 24 bytes of stack), the parts of its `scratch`, and what every
piece of it keeps (`KR`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Arm.FrameStack
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK SavedRegs saveR)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open VG.Proof.MdStream.Arm (Upd)
open Spec.Sha256 (bytesAt)

/-- The functions `pbkdf2` calls, verified. -/
structure FnsOK (F : Fns) where
  hH : HashOK F.H
  Wi : Nat
  Wf : Nat
  Wt : Nat
  hi : VG.Proof.Pbkdf2.Whole.Arm.Sound F.hiC (Spec.Hmac.initScratchContract hH.SH Wi Arm.abi 16)
  hf : VG.Proof.Pbkdf2.Whole.Arm.Sound F.hfC (Spec.Hmac.finalizeScratchContract hH.SH Wf Arm.abi 16)
  it : VG.Proof.Pbkdf2.Whole.Arm.Sound F.itC (Spec.Pbkdf2.iterateContract hH.SH Wt Arm.abi 16)
  hiSt : armStack F.hiC ≤ 16
  hfSt : armStack F.hfC ≤ 16
  itSt : armStack F.itC ≤ 16
  hWi : Wi ≤ F.W
  hWf : Wf ≤ F.W
  hWt : Wt ≤ F.W
  hWH : F.H.W ≤ F.W
  /-- The digest is no longer than a block (so that the digest of a long
  password is a key `init` takes). -/
  hDB : F.H.D ≤ F.H.B
  /-- The streaming state holds a block. -/
  hBS : F.H.B ≤ F.H.S
  /-- Our buffers fit in the `8 S` bytes after the working space. -/
  fits : 40 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S
  /-- And `scratch` is within reach of an immediate offset. -/
  reach : (F.W + F.H.S) * 8 ≤ 4096
  /-- The immediates the code compares and adds. -/
  encB1 : encodable (BitVec.ofNat 32 (F.H.B + 1)) = true
  encB : encodable (BitVec.ofNat 32 F.H.B) = true
  encB4 : encodable (BitVec.ofNat 32 (F.H.B + 4)) = true
  encD : encodable (BitVec.ofNat 32 F.H.D) = true

variable {F : Fns}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : BitVec 32 := s₀.gpr .r0
abbrev pwl : Nat := (s₀.gpr .r1).toNat
abbrev salt : BitVec 32 := s₀.gpr .r2
abbrev sl : Nat := (s₀.gpr .r3).toNat
/-- The iteration count. -/
abbrev cc : Nat := (VG.Arm.stackArg s₀ 0).toNat
abbrev out : BitVec 32 := VG.Arm.stackArg s₀ 1
abbrev ol : Nat := (VG.Arm.stackArg s₀ 2).toNat
abbrev scr : BitVec 32 := VG.Arm.stackArg s₀ 3
abbrev pwR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.pw s₀), VG.Proof.Pbkdf2.Whole.Arm.pwl s₀⟩
abbrev saltR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.salt s₀), VG.Proof.Pbkdf2.Whole.Arm.sl s₀⟩
abbrev outR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.out s₀), VG.Proof.Pbkdf2.Whole.Arm.ol s₀⟩
abbrev scR (F : Fns) : Region := ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.scr s₀), (F.W + F.H.S) * 8⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev stkR : Region := VG.Proof.Pbkdf2.Whole.Arm.stk s₀
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := VG.Proof.Pbkdf2.Whole.Arm.scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := State.addr (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨VG.Proof.Pbkdf2.Whole.Arm.A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨State.addr (VG.Proof.Pbkdf2.Whole.Arm.scr s₀), k⟩

end

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

/-- The size of `scratch`. -/
abbrev _root_.VG.Impl.Pbkdf2.Whole.Arm.Fns.L8 (F : Fns) : Nat := (F.W + F.H.S) * 8

/-- The precondition. -/
structure Pre (F : Fns) (s₀ : State) : Prop where
  sp24 : 24 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 16 ≤ 2 ^ 32
  rd : s₀.rd = [VG.Proof.Pbkdf2.Whole.Arm.pwR s₀, VG.Proof.Pbkdf2.Whole.Arm.saltR s₀, VG.Proof.Pbkdf2.Whole.Arm.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Whole.Arm.outR s₀, VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F]
  pw_o : (VG.Proof.Pbkdf2.Whole.Arm.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.outR s₀)
  pw_s : (VG.Proof.Pbkdf2.Whole.Arm.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F)
  sa_o : (VG.Proof.Pbkdf2.Whole.Arm.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.outR s₀)
  sa_s : (VG.Proof.Pbkdf2.Whole.Arm.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F)
  o_s : (VG.Proof.Pbkdf2.Whole.Arm.outR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F)
  o_a : (VG.Proof.Pbkdf2.Whole.Arm.outR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.argR s₀)
  s_a : (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.argR s₀)
  b_pw : (VG.Proof.Pbkdf2.Whole.Arm.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.pwR s₀)
  b_sa : (VG.Proof.Pbkdf2.Whole.Arm.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.saltR s₀)
  b_o : (VG.Proof.Pbkdf2.Whole.Arm.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.outR s₀)
  b_s : (VG.Proof.Pbkdf2.Whole.Arm.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F)
  b_a : (VG.Proof.Pbkdf2.Whole.Arm.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.argR s₀)
  npw : (VG.Proof.Pbkdf2.Whole.Arm.pw s₀).toNat + VG.Proof.Pbkdf2.Whole.Arm.pwl s₀ ≤ 2 ^ 32
  nsa : (VG.Proof.Pbkdf2.Whole.Arm.salt s₀).toNat + VG.Proof.Pbkdf2.Whole.Arm.sl s₀ ≤ 2 ^ 32
  no : (VG.Proof.Pbkdf2.Whole.Arm.out s₀).toNat + VG.Proof.Pbkdf2.Whole.Arm.ol s₀ ≤ 2 ^ 32
  nsc : (VG.Proof.Pbkdf2.Whole.Arm.scr s₀).toNat + F.L8 ≤ 2 ^ 32
  c0 : 0 < VG.Proof.Pbkdf2.Whole.Arm.cc s₀
  olD : VG.Proof.Pbkdf2.Whole.Arm.ol s₀ ≤ (2 ^ 32 - 1) * F.H.D

theorem pre_of (hF : VG.Proof.Pbkdf2.Whole.Arm.FnsOK F) {s₀ : State}
    (h : (Spec.Pbkdf2.pbkdf2ScratchContract hF.hH.SH (F.W + F.H.S) Arm.abi 24).pre s₀) : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀ := by
  sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  have hD := hF.hH.hD
  rw [hD] at h21
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

/-! ## The layout of `scratch` -/

/-- The sizes, as facts about natural numbers. -/
structure Sizes (F : Fns) : Prop where
  B : 0 < F.H.B ∧ F.H.B ≤ 128
  S : 0 < F.H.S ∧ F.H.S ≤ 256
  D : 0 < F.H.D ∧ F.H.D ≤ F.H.F ∧ F.H.F ≤ 64
  W : F.H.W ≤ F.W
  DB : F.H.D ≤ F.H.B
  BS : F.H.B ≤ F.H.S
  fits : 40 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S
  reach : F.L8 ≤ 4096
  encB1 : encodable (BitVec.ofNat 32 (F.H.B + 1)) = true
  encB : encodable (BitVec.ofNat 32 F.H.B) = true
  encB4 : encodable (BitVec.ofNat 32 (F.H.B + 4)) = true
  encD : encodable (BitVec.ofNat 32 F.H.D) = true

theorem FnsOK.sizes (hF : VG.Proof.Pbkdf2.Whole.Arm.FnsOK F) : VG.Proof.Pbkdf2.Whole.Arm.Sizes F :=
  ⟨⟨hF.hH.hB0, hF.hH.hBB⟩, ⟨hF.hH.hS0, hF.hH.hSB⟩, ⟨hF.hH.hD0, hF.hH.hDF, hF.hH.hF⟩, hF.hWH, hF.hDB, hF.hBS,
    hF.fits, hF.reach, hF.encB1, hF.encB, hF.encB4, hF.encD⟩

/-- Where the parts of `scratch` are. -/
theorem layout : F.L.buf = 8 * F.W + 36 ∧ F.st0O = 8 * F.W + 36 ∧ F.st1O = 8 * F.W + 36 + F.H.S ∧
    F.stSO = 8 * F.W + 36 + 2 * F.H.S ∧ F.stWO = 8 * F.W + 36 + 3 * F.H.S ∧
    F.uO = 8 * F.W + 36 + 4 * F.H.S ∧ F.tO = 8 * F.W + 36 + 4 * F.H.S + F.H.D ∧
    F.hkO = 8 * F.W + 36 + 4 * F.H.S + 2 * F.H.D ∧ F.intO = 8 * F.W + 36 + 4 * F.H.S + 2 * F.H.D + F.H.F := by
  dsimp only [Fns.st0O, Fns.st1O, Fns.stSO, Fns.stWO, Fns.uO, Fns.tO, Fns.hkO, Fns.intO, Fns.L, Hash.buf]
  omega

theorem end_le (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F) : F.intO + 4 ≤ F.L8 := by
  have := VG.Proof.Pbkdf2.Whole.Arm.layout (F := F); have := hz.fits; simp only [Fns.L8]; omega

/-- The save area of our caller's registers. -/
abbrev svR (F : Fns) (s₀ : State) : Region := saveR F.L (VG.Proof.Pbkdf2.Whole.Arm.scr s₀)

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < F.L8) : State.addr (VG.Proof.Pbkdf2.Whole.Arm.dO s₀ o) = VG.Proof.Pbkdf2.Whole.Arm.A s₀ o := by
  have := hp.nsc; exact addr_add (by omega)

omit hz in
theorem dO_toNat {o : Nat} (ho : o < F.L8) : (VG.Proof.Pbkdf2.Whole.Arm.dO s₀ o).toNat = (VG.Proof.Pbkdf2.Whole.Arm.scr s₀).toNat + o := by
  have := hp.nsc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ F.L8) : Region.Sub (VG.Proof.Pbkdf2.Whole.Arm.sR s₀ o n) (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.L8) (hb : b + n ≤ F.L8) :
    Region.Disjoint (VG.Proof.Pbkdf2.Whole.Arm.sR s₀ a m) (VG.Proof.Pbkdf2.Whole.Arm.sR s₀ b n) := by
  have := hz.reach; exact Offset.disjoint _ h (by omega) (by omega)

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ F.L8) :
    Region.Disjoint (VG.Proof.Pbkdf2.Whole.Arm.lowR s₀ k) (VG.Proof.Pbkdf2.Whole.Arm.sR s₀ b n) := by
  have := hz.reach; exact Offset.base_disjoint _ hk (by omega)

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ F.L8) : Region.Sub (VG.Proof.Pbkdf2.Whole.Arm.lowR s₀ k) (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (VG.Proof.Pbkdf2.Whole.Arm.svR F s₀) (VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F) := by
  have := VG.Proof.Pbkdf2.Whole.Arm.end_le hz; have := VG.Proof.Pbkdf2.Whole.Arm.layout (F := F)
  exact Offset.sub_base _ (by show 8 * F.W + 36 ≤ F.L8; omega)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : 8 * F.W + 36 ≤ o) (hon : o + n ≤ F.L8) : (VG.Proof.Pbkdf2.Whole.Arm.svR F s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.sR s₀ o n) := by
  have := hz.reach; exact Offset.disjoint _ (Or.inl (by simp only [Fns.L]; omega)) (by simp only [Fns.L]; omega) (by omega)

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * F.W) : (VG.Proof.Pbkdf2.Whole.Arm.svR F s₀).Disjoint (VG.Proof.Pbkdf2.Whole.Arm.lowR s₀ k) := by
  have := hz.reach; have := VG.Proof.Pbkdf2.Whole.Arm.end_le hz; have := VG.Proof.Pbkdf2.Whole.Arm.layout (F := F)
  exact (Offset.base_disjoint _ (k := k) (e := 8 * F.L.W) (n := 36) (by simp only [Fns.L]; omega)
    (by simp only [Fns.L]; omega)).symm

omit hz in
theorem sc_mem : VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F ∈ s₀.wr := by rw [hp.wr]; simp

theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.L8) :
    InRegions s.wr (VG.Proof.Pbkdf2.Whole.Arm.A s₀ o) n := by
  have := hz.reach
  exact ⟨VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, by rw [hwr]; exact VG.Proof.Pbkdf2.Whole.Arm.sc_mem hp, Offset.contains_base _ h (by omega)⟩

end

/-! ## What every piece keeps -/

/-- The regions everything writes: `out`, `scratch` and the stack below the stack pointer. -/
abbrev wrs (F : Fns) (s₀ : State) : List Region := [VG.Proof.Pbkdf2.Whole.Arm.outR s₀, VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, VG.Proof.Pbkdf2.Whole.Arm.stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (F : Fns) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = VG.Proof.Pbkdf2.Whole.Arm.salt s₀
  r6 : s.gpr .r6 = s₀.gpr .r3
  r11 : s.gpr .r11 = VG.Proof.Pbkdf2.Whole.Arm.scr s₀
  saved : SavedRegs F.L (VG.Proof.Pbkdf2.Whole.Arm.scr s₀) s₀ s.mem
  frame : Frame (VG.Proof.Pbkdf2.Whole.Arm.wrs F s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r5, .r6, .r11]

theorem kregs_pres : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.kregs, r ∈ preserved ∧ r ≠ .lr := by decide

/-- The 24 bytes below the stack pointer, while `KR` holds. -/
theorem KR.stkE {s₀ s : State} (h : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) : VG.Proof.Pbkdf2.Whole.Arm.stk s = VG.Proof.Pbkdf2.Whole.Arm.stkR s₀ := by
  show (⟨State.addr s.sp - 24, 24⟩ : Region) = ⟨State.addr s₀.sp - 24, 24⟩; rw [h.sp]

/-- `KR` survives changes to other registers, and to memory in `out`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Whole.Arm.svR F s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.Pbkdf2.Whole.Arm.wrs F s₀, Region.Sub r r') :
    VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r6,
    (hg _ (by simp)).trans h.r11, h.saved.frame F.L hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Whole.Arm.kregs) {v : BitVec 32}
    (u : Upd s s' d v) : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A write to a part of `scratch` after the save area. -/
theorem KR.write {s₀ s s' : State} (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F) (h : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.kregs, s'.gpr r = s.gpr r) {o n : Nat} (ho : 8 * F.W + 36 ≤ o)
    (hon : o + n ≤ F.L8) (hf : Frame [VG.Proof.Pbkdf2.Whole.Arm.sR s₀ o n] s.mem s'.mem) : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s' :=
  h.keep hrd hwr hsp hg hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Whole.Arm.sv_disj hz ho hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, VG.Proof.Pbkdf2.Whole.Arm.part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after the save area, or
the working space, and the stack below the stack pointer. -/
theorem KR.call {s₀ s s' : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.Arm.Sizes F) (h : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {ws : List Region}
    (ha : VG.Proof.Pbkdf2.Whole.Arm.After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = VG.Proof.Pbkdf2.Whole.Arm.lowR s₀ k ∧ k ≤ 8 * F.W) ∨
      ∃ o n, r = VG.Proof.Pbkdf2.Whole.Arm.sR s₀ o n ∧ 8 * F.W + 36 ≤ o ∧ o + n ≤ F.L8) : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s' := by
  have hL := VG.Proof.Pbkdf2.Whole.Arm.end_le hz; have := VG.Proof.Pbkdf2.Whole.Arm.layout (F := F)
  have f := ha.frame
  rw [h.stkE] at f
  refine h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Whole.Arm.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Whole.Arm.kregs_pres r hr).2) f
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact VG.Proof.Pbkdf2.Whole.Arm.sv_low hz hk
      · exact VG.Proof.Pbkdf2.Whole.Arm.sv_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hp.b_s.sub_right (VG.Proof.Pbkdf2.Whole.Arm.sv_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact ⟨VG.Proof.Pbkdf2.Whole.Arm.scR s₀ F, by simp, VG.Proof.Pbkdf2.Whole.Arm.low_sub (F := F) (by omega)⟩
      · exact ⟨_, by simp, VG.Proof.Pbkdf2.Whole.Arm.part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

/-! ## The stack arguments and the inputs, while `KR` holds -/

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.Arm.Pre F s₀)
include hp

theorem argR_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨stackArgAddr s₀ i, 4⟩ (VG.Proof.Pbkdf2.Whole.Arm.argR s₀) := by
  have e : stackArgAddr s₀ i = State.addr s₀.sp + BitVec.ofNat 64 (4 * i) := addr_add (by have := hp.spf; omega)
  have e0 : stackArgAddr s₀ 0 = State.addr s₀.sp := by simp [stackArgAddr]
  show Region.Sub ⟨stackArgAddr s₀ i, 4⟩ ⟨stackArgAddr s₀ 0, 16⟩
  rw [e, e0]
  exact Offset.sub_base _ (by omega)

theorem KR.stackArg {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {i : Nat} (hi : i < 4) : VG.Arm.stackArg s i = VG.Arm.stackArg s₀ i := by
  have ea : stackArgAddr s i = stackArgAddr s₀ i := by simp only [stackArgAddr, hk.sp]
  show s.mem.readW (stackArgAddr s i) 32 = s₀.mem.readW (stackArgAddr s₀ i) 32
  rw [ea]
  refine hk.frame.readW (r := ⟨stackArgAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.o_a.symm.sub_left (VG.Proof.Pbkdf2.Whole.Arm.argR_sub hp hi))
  · exact (hp.s_a.symm.sub_left (VG.Proof.Pbkdf2.Whole.Arm.argR_sub hp hi))
  · exact (hp.b_a.symm.sub_left (VG.Proof.Pbkdf2.Whole.Arm.argR_sub hp hi))

theorem argIn {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := by
  rw [hk.rd, hk.wr, hp.rd, hp.wr, hk.sp]
  have e : State.addr (s₀.sp + BitVec.ofNat 32 (4 * i)) = State.addr s₀.sp + BitVec.ofNat 64 (4 * i) :=
    addr_add (by have := hp.spf; omega)
  have e0 : stackArgAddr s₀ 0 = State.addr s₀.sp := by simp [stackArgAddr]
  refine ⟨VG.Proof.Pbkdf2.Whole.Arm.argR s₀, by simp, ?_⟩
  show Region.Contains ⟨stackArgAddr s₀ 0, 16⟩ _ 4
  rw [e, e0]
  exact Offset.contains_base _ (by omega) (by omega)

/-- `ldr d, [sp, #4 i]`: stack argument `i`, while `KR` holds. -/
theorem wp_arg {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {d : Reg} {i : Nat} (hi : i < 4) {is : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' d (VG.Arm.stackArg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp d (4 * i) :: is)) s Q :=
  VG.Proof.MdStream.Arm.wp_ldrSp (a := State.addr (s.sp + BitVec.ofNat 32 (4 * i))) (by omega) rfl
    (VG.Proof.Pbkdf2.Whole.Arm.argIn hp hk hi) fun s' u => k s' (by rw [← hk.stackArg hp hi]; exact u)

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {p : Addr} {n : Nat} (hd : ∀ r ∈ VG.Proof.Pbkdf2.Whole.Arm.wrs F s₀, Region.Disjoint ⟨p, n⟩ r)
    (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep hk.frame hd hn

theorem KR.pwBytes {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) :
    bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.pw s₀)) (VG.Proof.Pbkdf2.Whole.Arm.pwl s₀) = bytesAt s₀.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.pw s₀)) (VG.Proof.Pbkdf2.Whole.Arm.pwl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.b_pw.symm) (by have := hp.npw; omega)

theorem KR.saltBytes {s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) :
    bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.salt s₀)) (VG.Proof.Pbkdf2.Whole.Arm.sl s₀) = bytesAt s₀.mem (State.addr (VG.Proof.Pbkdf2.Whole.Arm.salt s₀)) (VG.Proof.Pbkdf2.Whole.Arm.sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.b_sa.symm) (by have := hp.nsa; omega)

end

/-! ## One instruction at a time -/

/-- `s'` is `s` with registers `d` set to `v` and `r12` changed. -/
structure Upd12 (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → r ≠ .r12 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem KR.upd12 {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Whole.Arm.kregs) {v : BitVec 32}
    (u : VG.Proof.Pbkdf2.Whole.Arm.Upd12 s s' d v) : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r (fun e => hd (e ▸ hr)) (by
    simp only [VG.Proof.Pbkdf2.Whole.Arm.kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    u.mem

/-- `d ← scratch + o` (through `r12`), while `KR` holds. -/
theorem scr_ok {s₀ s : State} (hk : VG.Proof.Pbkdf2.Whole.Arm.KR F s₀ s) {d : Reg} {o : Nat} (ho : o < 2 ^ 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Whole.Arm.Upd12 s s' d (VG.Proof.Pbkdf2.Whole.Arm.dO s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (scrAt d o ++ rest)) s Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine Pbkdf2.Stream.Arm.wp_movw fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_reg _ _)
    fun s₂ u₂ => k s₂ ⟨?_, fun r h₁ h₂ => by rw [u₂.other r h₁, u₁.other r h₂], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩
  rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hk.r11, Pbkdf2.Stream.Arm.movw_ofNat ho]

/-- `adc d, n, #y`. -/
theorem wp_adc {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → s'.c = s.c → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0))) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _) rfl)

/-- `subs d, n, op2`, with its carry: whether `n ≥ op2`. -/
theorem wp_subsC {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

/-- `mov d, op2`, keeping the carry. -/
theorem wp_movC {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {o : Op2} {v : BitVec 32}
    (ho : o.eval s = some v) (k : ∀ s', Upd s s' d v → s'.c = s.c → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d v) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _) rfl)

/-- `subs r12, x, #k; mov r12, #0; adc r12, r12, #0; cmp r12, #0`: `Z` is
whether `x < k`, and only `r12` and the flags change. -/
theorem wp_lt {is : List Instr} {s : State} {Q : State → Prop} {x : Reg} {k : BitVec 32}
    (hk : encodable k = true)
    (h : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → s'.z = decide ((s.gpr x).toNat < k.toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs .r12 x (.imm k) :: .mov .r12 (.imm 0) :: .adc .r12 .r12 (.imm 0) :: .cmp .r12 (.imm 0) :: is))
      s Q := by
  refine VG.Proof.Pbkdf2.Whole.Arm.wp_subsC (VG.Proof.MdStream.Arm.op2_imm hk) fun s₁ u₁ c₁ => VG.Proof.Pbkdf2.Whole.Arm.wp_movC
    (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ u₂ c₂ => VG.Proof.Pbkdf2.Whole.Arm.wp_adc (VG.Proof.MdStream.Arm.op2_imm (by decide))
    fun s₃ u₃ c₃ => VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₄ f₄ z₄ =>
      h s₄ (fun r hr => by rw [f₄.gpr, u₃.other r hr, u₂.other r hr, u₁.other r hr]) (by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem])
        (by rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [f₄.sp, u₃.sp, u₂.sp, u₁.sp]) ?_
  rw [z₄, u₃.gpr, u₂.gpr, c₂, c₁]
  by_cases hlt : (s.gpr x).toNat < k.toNat
  · simp [hlt, show ¬ (k.toNat ≤ (s.gpr x).toNat) by omega]
  · simp [hlt, show k.toNat ≤ (s.gpr x).toNat by omega]

end VG.Proof.Pbkdf2.Whole.Arm

end
