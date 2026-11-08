module

public import VerifiedGarbage.Impl.Gcm.X86_64.Flag
public import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.X86_64.WidenArray
import VerifiedGarbage.Proof.Framework.PostMono
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# Choosing on the prepared key context's count of powers, on x86-64

`onFlag t c₁ c₂` (`Impl/Gcm/X86_64/Flag.lean`) reads the word at
`rdi + 1024` into `rax` and compares it with `t`, writing only `rax` and the
flags, which no contract reads (`Same`): so a contract built by
`Sig.contract` holds of the state after it as of the state before
(`pre_same`, `post_same`, `pub_same`). It then runs `c₁` if the word is at
least `t` (the `t` powers it reads are there) and `c₂` if not (the code that
reads only the key context).
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.Gcm.X86_64.Flag VG.X86_64.RegUpd

/-- `u` is `s` but for `rax` and the flags. -/
structure Same (s u : State) : Prop where
  gpr : ∀ r, r ≠ .rax → u.gpr r = s.gpr r
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mx : u.mxcsr = s.mxcsr

theorem Same.abi {s u s' : State} (h : Same s u) (a : abiPreserved u s') : abiPreserved s s' :=
  ⟨fun r hr => by rw [a.1 r hr, h.gpr r (by rintro rfl; simp [calleeSaved] at hr)],
    by rw [← h.gpr .rsp (by decide), a.2.1, h.mem], by rw [a.2.2, h.mx]⟩

/-- `testFlag t` from `s`: it reads the word at `rdi + 1024`, and clears CF if
it is at least `t`. -/
theorem testFlag_run {t : Nat} (htv : t = 16 ∨ t = 48) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + 1024) 8) :
    ∃ u, execBlock isa (testFlag t) s = some (u, [.addr (s.gpr .rdi + 1024)]) ∧ Same s u ∧
      eval .ae u = some (decide (t ≤ (s.mem.readW (s.gpr .rdi + 1024) 64).toNat)) := by
  have ea : s.ea { base := .rdi, disp := flagOff } = s.gpr .rdi + 1024 := rfl
  refine ⟨?u, ?h1, ⟨?h2, ?h3, ?h4, ?h5, ?h6⟩, ?h7⟩
  case h1 =>
    simp only [execBlock, testFlag, exec, readSrc, ea, addrs, srcAddrs, State.load64, hin, ↓reduceIte]
    rfl
  case h3 => rfl
  case h4 => rfl
  case h5 => rfl
  case h6 => rfl
  case h2 =>
    intro r hr
    simp only [gpr_arithFlags, gpr_setReg, hr, ↓reduceIte]
  case h7 =>
    simp only [eval, cf_arithFlags, gpr_setReg, ↓reduceIte, Option.map_some]
    have e : ((BitVec.ofNat 32 t).signExtend 64).toNat = t := by
      rcases htv with rfl | rfl <;> rfl
    simp only [e, Option.some.injEq]
    generalize (s.mem.readW _ 64).toNat = x
    by_cases h : t ≤ x <;> simp [h] <;> omega

/-! ## What a contract reads is the same after the test -/

theorem Same.stackArg_eq {s u : State} (h : Same s u) (i : Nat) :
    VG.X86_64.stackArg u i = VG.X86_64.stackArg s i := by
  simp only [VG.X86_64.stackArg, stackArgAddr, h.gpr .rsp (by decide), h.mem]

theorem args_same {ws : List Nat} {vals : State → List (BitVec 64)} (hv : abi.args ws = some vals)
    {s u : State} (h : Same s u) : vals u = vals s := by
  simp only [abi] at hv
  split at hv <;> cases hv
  · dsimp only
    exact List.map_congr_left fun r hr => h.gpr r (by
      rintro rfl; exact absurd (List.mem_of_mem_take hr) (by decide : Reg.rax ∉ argRegs))
  · dsimp only
    rw [List.map_congr_left (l := argRegs) fun r hr => h.gpr r (by
        rintro rfl; exact absurd hr (by decide : Reg.rax ∉ argRegs)),
      List.map_congr_left (l := List.range _) fun i _ => h.stackArg_eq i]

variable {sig : Sig} {pre : Curry (sig.words 64) (Mem → Prop)} {post : sig.Post 64} {wa : Bool}
  {stack : Nat} {leak : Option (Curry (sig.words 64) (Mem → List Nat))}

theorem pre_same {s u : State} (h : Same s u) :
    (sig.contract abi pre post wa stack leak).pre u ↔ (sig.contract abi pre post wa stack leak).pre s := by
  have hsp := h.gpr .rsp (by decide)
  dsimp only [Sig.contract]
  split
  · exact Iff.rfl
  rename_i vals hv
  have ev := args_same hv h
  have em : abi.mem u = abi.mem s := h.mem
  have erd : abi.rd u = abi.rd s := h.rd
  have ewr : abi.wr u = abi.wr s := h.wr
  have ea (W : List Nat) : abi.argArea W u = abi.argArea W s := by
    simp only [abi, stackArgAddr, hsp]
  have er (n : Nat) : abi.reserved n u = abi.reserved n s := by simp only [abi, hsp]
  have ew (W : List Nat) (n : Nat) : abi.wf W n u = abi.wf W n s := by simp only [abi, hsp]
  rw [ev, em, erd, ewr, ea, er, ew]

theorem post_same {s u s' : State} (h : Same s u) :
    (sig.contract abi pre post wa stack leak).post u s' ↔ (sig.contract abi pre post wa stack leak).post s s' := by
  dsimp only [Sig.contract]
  split
  · exact Iff.rfl
  rename_i vals hv
  have em : abi.mem u = abi.mem s := h.mem
  rw [args_same hv h, em]

theorem pub_same {s u s' u' : State} (h : Same s u) (h' : Same s' u') :
    (sig.contract abi pre post wa stack leak).pub u u' ↔ (sig.contract abi pre post wa stack leak).pub s s' := by
  dsimp only [Sig.contract]
  split
  · exact Iff.rfl
  rename_i vals hv
  have em : abi.mem u = abi.mem s := h.mem
  have em' : abi.mem u' = abi.mem s' := h'.mem
  have ep : abi.pub u u' = abi.pub s s' := by
    simp only [abi, h.gpr .rsp (by decide), h'.gpr .rsp (by decide)]
  rw [args_same hv h, args_same hv h', em, em', ep]

/-! ## The choice -/

/-- The count at `rdi + 1024`. -/
abbrev flagCount (s : State) : Nat := (s.mem.readW (s.gpr .rdi + 1024) 64).toNat

/-- `onFlag t c₁ c₂` against `k`, from `c₁` against `k₁` and `c₂` against
`k₂` (contracts of the same signature and postcondition): from `k`'s
precondition, the count at `rdi + 1024` is readable, and `k₁`'s precondition
holds if it is at least `t` and `k₂`'s if not; and two runs with the same
public data have the same `rdi` and agree on whether the count is at least
`t`, and have the same public data for `k₁` and `k₂`. -/
theorem Verified.of_onFlag {t : Nat} (htv : t = 16 ∨ t = 48) {c₁ c₂ : Prog isa} {pre₁ pre₂ : Curry (sig.words 64) (Mem → Prop)}
    {leak₁ leak₂ : Option (Curry (sig.words 64) (Mem → List Nat))}
    (h₁ : Verified target c₁ (sig.contract abi pre₁ post wa stack leak₁))
    (h₂ : Verified target c₂ (sig.contract abi pre₂ post wa stack leak₂))
    (hin : ∀ s, (sig.contract abi pre post wa stack leak).pre s →
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + 1024) 8)
    (hp₁ : ∀ s, (sig.contract abi pre post wa stack leak).pre s → t ≤ flagCount s →
      (sig.contract abi pre₁ post wa stack leak₁).pre s)
    (hp₂ : ∀ s, (sig.contract abi pre post wa stack leak).pre s → ¬ t ≤ flagCount s →
      (sig.contract abi pre₂ post wa stack leak₂).pre s)
    (hpub : ∀ s s', (sig.contract abi pre post wa stack leak).pre s →
      (sig.contract abi pre post wa stack leak).pre s' →
      (sig.contract abi pre post wa stack leak).pub s s' →
      s.gpr .rdi = s'.gpr .rdi ∧ (t ≤ flagCount s ↔ t ≤ flagCount s') ∧
      (sig.contract abi pre₁ post wa stack leak₁).pub s s' ∧
      (sig.contract abi pre₂ post wa stack leak₂).pub s s')
    (hsat : ∃ s, (sig.contract abi pre post wa stack leak).pre s) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag t c₁ c₂) (sig.contract abi pre post wa stack leak) := by
  have run (s : State) (hs : (sig.contract abi pre post wa stack leak).pre s) :=
    testFlag_run htv s (hin s hs)
  refine Verified.entryBranch (p := fun s => decide (t ≤ flagCount s))
    (fun s => [.addr (s.gpr .rdi + 1024)]) h₁ h₂ (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, hS, ev⟩ := run s hs
    refine ⟨u, e, ev, fun hp => ⟨(pre_same hS).mpr (hp₁ s hs (of_decide_eq_true hp)),
        fun s' a q => ⟨hS.abi a, (post_same hS).mp q⟩⟩,
      fun hp => ⟨(pre_same hS).mpr (hp₂ s hs (by simpa using hp)),
        fun s' a q => ⟨hS.abi a, (post_same hS).mp q⟩⟩⟩
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, hS, -⟩ := run s hs
    obtain ⟨u₀', e₀', hS', -⟩ := run s' hs'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    obtain ⟨hr, hz, q₁, q₂⟩ := hpub s s' hs hs' hq
    refine ⟨by rw [hr], ?_, fun _ => (pub_same hS hS').mpr q₁, fun _ => (pub_same hS hS').mpr q₂⟩
    simp only [hz]

/-! ## For a first argument that is the prepared key context -/

/-- The first argument `abi` reads is `rdi`. -/
theorem abi_args_rdi {ws : List Nat} {vals : State → List (BitVec 64)}
    (h : abi.args ws = some vals) (hws : ws ≠ []) (s : State) :
    ∃ vs, vals s = s.gpr .rdi :: vs := by
  simp only [abi] at h
  split at h <;> cases h
  · cases ws with
    | nil => exact absurd rfl hws
    | cons w ws => exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- What the count at `ctx + 1024` leaks: whether it is at least 48, at least
16, or less. -/
abbrev flagLeak (m : Mem) (ctx : Addr) : Nat :=
  if 48 ≤ (m.readW (ctx + 1024) 64).toNat then 2
  else if 16 ≤ (m.readW (ctx + 1024) 64).toNat then 1 else 0

/-- Two counts of the same `flagLeak` are both at least 16, or both not, and
both at least 48, or both not. -/
theorem flagLeak_iff {t : Nat} (htv : t = 16 ∨ t = 48) {m m' : Mem} {p p' : Addr}
    (h : flagLeak m p = flagLeak m' p') :
    t ≤ (m.readW (p + 1024) 64).toNat ↔ t ≤ (m'.readW (p' + 1024) 64).toNat := by
  simp only [flagLeak] at h
  generalize (m.readW (p + 1024) 64).toNat = a at h ⊢
  generalize (m'.readW (p' + 1024) 64).toNat = b at h ⊢
  by_cases h48a : 48 ≤ a <;> by_cases h48b : 48 ≤ b <;> by_cases h16a : 16 ≤ a <;>
    by_cases h16b : 16 ≤ b <;> simp only [h48a, h48b, h16a, h16b, ↓reduceIte] at h <;>
    rcases htv with rfl | rfl <;> omega

theorem Curry.apply_const' {α : Type} (a : α) :
    ∀ (ws : List ArgWord) (vs : List (BitVec 64)), Curry.apply ws (Curry.const a ws) vs = a
  | [], _ => rfl
  | _ :: ws, [] => Curry.apply_const' a ws []
  | _ :: ws, _ :: vs => Curry.apply_const' a ws vs

/-- The signature `params` with a first array of `n` elements of `e`, named
`name`, writable if `w`. -/
abbrev firstArraySigB (name : String) (w : Bool) (e : Elem) (n : Nat) (rest : List (String × Param))
    (ret : Option IntTy) : Sig :=
  { params := (name, .array w e n) :: rest, ret := ret }

section
variable {name : String} {w : Bool} {N : Nat} {rest : List (String × Param)} {ret : Option IntTy}
  {post : (firstArraySigB name w .u64 N rest ret).Post 64} {wa : Bool} {stack : Nat}

/-- A precondition that, given the first argument and a condition `C` on it
and memory, implies another, implies it of the states whose `rdi` and
memory satisfy `C`. -/
theorem pre_of_rel {C : Mem → Addr → Prop} {leakA leakB : Option (Curry
      ((firstArraySigB name w .u64 N rest ret).words 64) (Mem → List Nat))}
    {pre pre' : Curry ((firstArraySigB name w .u64 N rest ret).words 64) (Mem → Prop)}
    (R : ∀ ctx, Curry.Forall₂ (fun p q => ∀ m, p m → C m ctx → q m) _ (pre ctx) (pre' ctx))
    {s : State} (hs : ((firstArraySigB name w .u64 N rest ret).contract abi pre post wa stack leakA).pre s)
    (hc : C s.mem (s.gpr .rdi)) :
    ((firstArraySigB name w .u64 N rest ret).contract abi pre' post wa stack leakB).pre s := by
  dsimp only [Sig.contract] at hs ⊢
  split at hs
  · exact hs.elim
  rename_i vals hv
  have hne : List.map (fun x => ArgWord.bits abi.ptrBits x)
      ((firstArraySigB name w .u64 N rest ret).words abi.ptrBits) ≠ [] := by
    simp [Sig.words, Param.words]
  obtain ⟨vs, hvs⟩ := abi_args_rdi hv hne s
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hs
  refine ⟨a1, a2, a3, a4, a5, a6, ?_⟩
  change Curry.apply _ pre' (vals s) s.mem
  change Curry.apply _ pre (vals s) s.mem at a7
  rw [hvs] at a7 ⊢
  exact (R (s.gpr .rdi)).apply vs s.mem a7 hc

/-- `Verified.of_onFlag` for a first argument that is an array of `N ≥ 129` words: the preconditions as relations between curried functions of the
other arguments, given the first; and `leak`, `leak₁`'s (none: nothing)
after `flagLeak`, the class of the count, for a threshold `t` of 16 or 48. -/
theorem Verified.of_onFlagCtx {t : Nat} (htv : t = 16 ∨ t = 48) (hN : 129 ≤ N) {c₁ c₂ : Prog isa}
    {pre pre₁ pre₂ : Curry ((firstArraySigB name w .u64 N rest ret).words 64) (Mem → Prop)}
    {leak₁ : Option (Curry ((firstArraySigB name w .u64 N rest ret).words 64) (Mem → List Nat))}
    {leak : Curry ((firstArraySigB name w .u64 N rest ret).words 64) (Mem → List Nat)}
    (h₁ : Verified target c₁ ((firstArraySigB name w .u64 N rest ret).contract abi pre₁ post wa stack leak₁))
    (h₂ : Verified target c₂ ((firstArraySigB name w .u64 N rest ret).contract abi pre₂ post wa stack leak₁))
    (hp₁ : ∀ ctx, Curry.Forall₂ (fun p q => ∀ m, p m → t ≤ (m.readW (ctx + 1024) 64).toNat → q m) _
      (pre ctx) (pre₁ ctx))
    (hp₂ : ∀ ctx, Curry.Forall₂ (fun p q => ∀ m, p m → ¬ t ≤ (m.readW (ctx + 1024) 64).toNat → q m) _
      (pre ctx) (pre₂ ctx))
    (hleak : ∀ ctx, Curry.Forall₂ (fun f g => ∀ m, f m = flagLeak m ctx :: g m) _
      (leak ctx) ((leak₁.getD (Curry.const (fun _ => []) _)) ctx))
    (hsat : ∃ s, ((firstArraySigB name w .u64 N rest ret).contract abi pre post wa stack (some leak)).pre s) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag t c₁ c₂)
      ((firstArraySigB name w .u64 N rest ret).contract abi pre post wa stack (some leak)) := by
  have hne : List.map (fun x => ArgWord.bits abi.ptrBits x)
      ((firstArraySigB name w .u64 N rest ret).words abi.ptrBits) ≠ [] := by
    simp [Sig.words, Param.words]
  refine Verified.of_onFlag htv h₁ h₂ ?_ ?_ ?_ ?_ hsat
  · intro s hs
    dsimp only [Sig.contract] at hs
    split at hs
    · exact hs.elim
    rename_i vals hv
    obtain ⟨vs, hvs⟩ := abi_args_rdi hv hne s
    obtain ⟨-, hrd, hwr, -⟩ := hs
    have hmem : (⟨s.gpr .rdi, N * Elem.size .u64⟩ : Region) ∈ s.rd ++ s.wr := by
      cases w
      · refine List.mem_append_left _ ?_
        change _ ∈ abi.rd s
        rw [hrd, hvs]
        simp [Sig.bufs]
      · refine List.mem_append_right _ ?_
        change _ ∈ abi.wr s
        rw [hwr, hvs]
        simp [Sig.bufs]
    refine ⟨_, hmem, ?_⟩
    simp only [Region.Contains]
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
    have h1 : (1024 : BitVec 64).toNat = 1024 := rfl
    simp only [Elem.size]
    omega
  · exact fun s hs hf => pre_of_rel (C := fun m ctx => t ≤ (m.readW (ctx + 1024) 64).toNat) hp₁ hs hf
  · exact fun s hs hf => pre_of_rel (C := fun m ctx => ¬ t ≤ (m.readW (ctx + 1024) 64).toNat) hp₂ hs hf
  · intro s s' _ _ hq
    dsimp only [Sig.contract] at hq ⊢
    split at hq
    · exact hq.elim
    rename_i vals hv
    obtain ⟨vs, hvs⟩ := abi_args_rdi hv hne s
    obtain ⟨vs', hvs'⟩ := abi_args_rdi hv hne s'
    obtain ⟨⟨hab, hl⟩, hpubs, hdescs⟩ := hq
    have hr : s.gpr .rdi = s'.gpr .rdi := by
      have h0 := hpubs 0 rfl
      rw [hvs, hvs'] at h0
      change (s.gpr .rdi).setWidth 64 = (s'.gpr .rdi).setWidth 64 at h0
      simpa using h0
    change Curry.apply _ leak (vals s) s.mem = Curry.apply _ leak (vals s') s'.mem at hl
    rw [hvs, hvs'] at hl
    change Curry.apply _ (leak (s.gpr .rdi)) vs s.mem =
      Curry.apply _ (leak (s'.gpr .rdi)) vs' s'.mem at hl
    rw [(hleak (s.gpr .rdi)).apply vs s.mem, (hleak (s'.gpr .rdi)).apply vs' s'.mem] at hl
    obtain ⟨hf, hrest⟩ := List.cons.inj hl
    refine ⟨hr, ?_, ⟨?k₁, hpubs, hdescs⟩, ⟨?k₂, hpubs, hdescs⟩⟩
    case k₁ =>
      cases leak₁ with
      | none => exact hab
      | some l =>
        refine ⟨hab, ?_⟩
        change Curry.apply _ l (vals s) s.mem = Curry.apply _ l (vals s') s'.mem
        rw [hvs, hvs']
        exact hrest
    case k₂ =>
      cases leak₁ with
      | none => exact hab
      | some l =>
        refine ⟨hab, ?_⟩
        change Curry.apply _ l (vals s) s.mem = Curry.apply _ l (vals s') s'.mem
        rw [hvs, hvs']
        exact hrest
    exact flagLeak_iff htv hf
end

/-! ## A longer writable first array -/

/-- The signature `params` with a writable first array of `n` elements of
`e`, named `name`. -/
abbrev firstArraySigW (name : String) (e : Elem) (n : Nat) (rest : List (String × Param))
    (ret : Option IntTy) : Sig :=
  { params := (name, .array true e n) :: rest, ret := ret }

/-- The regions `rs` extend themselves with the first narrowed. -/
theorem narrowHead_prefix (len : Nat) (rs : List Region) :
    List.Forall₂ Region.Prefix (narrowHead len rs) rs := by
  cases rs with
  | nil => exact .nil
  | cons r rs => exact .cons ⟨rfl, Nat.min_le_right ..⟩ (forall₂_prefix_refl _)

/-- The descriptors of `Sig.descs` do not depend on a writable array's length. -/
theorem descs_arrayW {name : String} {rest : List (String × Param)} (e : Elem) (n n' : Nat)
    (vs : List (BitVec 64)) :
    Sig.descs 64 ((name, .array true e n') :: rest) vs =
      Sig.descs 64 ((name, .array true e n) :: rest) vs := by
  cases vs <;> rfl

/-- Moving a proof to a longer writable first array, a stronger precondition
and a weaker postcondition, all else the same: the code writes only the
first `n` elements, as the shorter array's contract lets it. -/
theorem Verified.widenFirstArrayW {c : Prog isa} {name : String} {e : Elem} {n n' : Nat}
    (hn : n ≤ n') {rest : List (String × Param)} {ret : Option IntTy}
    {pre : Curry ((firstArraySigW name e n rest ret).words 64) (Mem → Prop)}
    {pre' : Curry ((firstArraySigW name e n' rest ret).words 64) (Mem → Prop)}
    {post : (firstArraySigW name e n rest ret).Post 64} {wa : Bool} {stack : Nat}
    {leak : Option (Curry ((firstArraySigW name e n rest ret).words 64) (Mem → List Nat))}
    (h : Verified target c ((firstArraySigW name e n rest ret).contract abi pre post wa stack leak))
    (hp : Curry.Forall₂ (fun p q => ∀ m, p m → q m) _ pre' pre)
    (hsat : ∃ s, ((firstArraySigW name e n' rest ret).contract abi pre' post wa stack leak).pre s) :
    Verified target c ((firstArraySigW name e n' rest ret).contract abi pre' post wa stack leak) := by
  refine regionModel.verified_widen (T := target) (fun _ _ _ _ h => h) h
    (fun s => narrowHead (n * e.size) s.wr) ?_ (fun _ _ => narrowHead_prefix _ _) ?_ ?_ hsat
  · intro s hs
    dsimp only [Sig.contract] at hs ⊢
    split at hs
    · exact hs.elim
    rename_i vals hvals
    split
    · rename_i h'; exact absurd (hvals.symm.trans h') nofun
    rename_i vals' hvals'
    obtain rfl : vals' = vals := Option.some.inj (hvals'.symm.trans hvals)
    have hw := abi_args_withRegions hvals s s.rd (narrowHead (n * e.size) s.wr)
    obtain ⟨p, vs, hv⟩ := abi_args_cons hvals (by simp [Sig.words, Param.words]) s
    have hW : List.map (fun x => ArgWord.bits abi.ptrBits x)
        ((firstArraySigW name e n rest ret).words abi.ptrBits) =
        List.map (fun x => ArgWord.bits abi.ptrBits x)
        ((firstArraySigW name e n' rest ret).words abi.ptrBits) := rfl
    simp only [regionModel, hw] at hs ⊢
    rw [hv] at hs ⊢
    simp only [Sig.bufs, Sig.lists, List.cons_append, List.filter_cons] at hs ⊢
    rw [hW]
    generalize List.map (fun x => ArgWord.bits abi.ptrBits x)
        ((firstArraySigW name e n' rest ret).words abi.ptrBits) = W at hs ⊢
    have hm : abi.mem (s.withRegions s.rd (narrowHead (n * e.size) s.wr)) = abi.mem s := rfl
    have ha : abi.argArea W (s.withRegions s.rd (narrowHead (n * e.size) s.wr)) =
      abi.argArea W s := rfl
    have hr : abi.reserved stack (s.withRegions s.rd (narrowHead (n * e.size) s.wr)) =
      abi.reserved stack s := rfl
    simp only [hm, ha, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.map_cons] at hs ⊢
    generalize Sig.bufs rest vs ++ List.map (fun r => (r, false))
      (Sig.lists abi.ptrBits (abi.mem s) rest vs) = B at hs ⊢
    obtain ⟨hwf, hrd, hwr, hpw, hres, hb, hpre⟩ := hs
    have hsub : Region.Sub ⟨p, n * e.size⟩ ⟨p, n' * e.size⟩ :=
      Region.sub_prefix (Nat.mul_le_mul_right _ hn)
    refine ⟨hwf, hrd, ?_, ?_, ?_, ?_, ?_⟩
    · change narrowHead (n * e.size) (abi.wr s) = _
      rw [hwr, narrowHead, Nat.min_eq_left (Nat.mul_le_mul_right _ hn)]
    · rw [List.pairwise_cons] at hpw ⊢
      exact ⟨fun b hb hd => (hpw.1 b hb hd).sub_left hsub, hpw.2⟩
    · intro r hr' a ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact (hres r hr' _ (List.mem_cons_self ..)).sub_right hsub
      · exact hres r hr' a (List.mem_cons_of_mem _ ha')
    · intro a ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · have := hb _ (List.mem_cons_self ..)
        have := Nat.mul_le_mul_right e.size hn
        dsimp only at *; omega
      · exact hb a (List.mem_cons_of_mem _ ha')
    · exact hp.apply _ _ hpre
  · intro s s' _ h
    dsimp only [Sig.contract] at h ⊢
    split at h
    · exact h.elim
    rename_i vals hvals
    split
    · rename_i h'; exact absurd (hvals.symm.trans h') nofun
    rename_i vals' hvals'
    obtain rfl : vals' = vals := Option.some.inj (hvals'.symm.trans hvals)
    simp only [regionModel, abi_args_withRegions hvals] at h
    exact h
  · intro s₁ s₂ _ _ h
    dsimp only [Sig.contract] at h ⊢
    split at h
    · exact h.elim
    rename_i vals hvals
    split
    · rename_i h'; exact absurd (hvals.symm.trans h') nofun
    rename_i vals' hvals'
    obtain rfl : vals' = vals := Option.some.inj (hvals'.symm.trans hvals)
    have hm (s : State) : abi.mem (s.withRegions s.rd (narrowHead (n * e.size) s.wr)) = abi.mem s :=
      rfl
    have hq : abi.pub (s₁.withRegions s₁.rd (narrowHead (n * e.size) s₁.wr))
      (s₂.withRegions s₂.rd (narrowHead (n * e.size) s₂.wr)) = abi.pub s₁ s₂ := rfl
    simp only [regionModel, abi_args_withRegions hvals, hm, hq]
    refine ⟨?_, h.2.1, ?_⟩
    · cases leak
      · exact h.1
      · exact h.1
    · exact (descs_arrayW (name := name) (rest := rest) e n n' (vals' s₁)) ▸ h.2.2


/-! ## More stack -/

/-- A function whose calls and frames use `n` bytes of stack below the stack
pointer meets the same contract with more, `n'`, reserved for them. -/
theorem Verified.stack_mono {c : Prog isa} {sig : Sig} {pre : Curry (sig.words 64) (Mem → Prop)}
    {post : sig.Post 64} {wa : Bool} {n n' : Nat}
    {leak : Option (Curry (sig.words 64) (Mem → List Nat))} (hn : n ≤ n')
    (h : Verified target c (sig.contract abi pre post wa n leak))
    (hsat : ∃ s, (sig.contract abi pre post wa n' leak).pre s) :
    Verified target c (sig.contract abi pre post wa n' leak) := by
  refine h.of_implies ⟨fun s hs => ?_, fun _ _ _ q => q, fun _ _ _ _ q => q, hsat⟩
  dsimp only [Sig.contract] at hs ⊢
  split at hs
  · exact hs.elim
  obtain ⟨w, rd, wr, pw, res, b, p⟩ := hs
  refine ⟨?_, rd, wr, pw, fun r hr a ha => ?_, b, p⟩
  · simp only [abi] at w ⊢
    split at w <;> rename_i hl <;> simp only [hl, ↓reduceIte] at w ⊢
    · cases n with
      | zero => trivial
      | succ k => cases n' with
        | zero => omega
        | succ k' =>
          have w' : k' + 1 ≤ (s.gpr .rsp).toNat := w
          show k + 1 ≤ (s.gpr .rsp).toNat
          omega
    · refine ⟨?_, w.2⟩
      cases n with
      | zero => trivial
      | succ k => cases n' with
        | zero => omega
        | succ k' =>
          have w' : k' + 1 ≤ (s.gpr .rsp).toNat := w.1
          show k + 1 ≤ (s.gpr .rsp).toNat
          omega
  · simp only [abi] at hr res
    rcases List.mem_cons.mp hr with rfl | hr
    · exact res _ List.mem_cons_self a ha
    · cases n with
      | zero => simp [stackBelow] at hr
      | succ k =>
        cases n' with
        | zero => omega
        | succ k' =>
          simp only [stackBelow, List.mem_singleton] at hr
          subst hr
          exact (res _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) a ha).sub_left
            (Offset.sub_below _ (a := k + 1) (n := k + 1) (b := k' + 1) (m := k' + 1) (by omega)
              (by omega))

/-! ## Leaking more -/

section
variable {T : Target} {c : Prog T.isa} {A : Abi T.isa} {sig : Sig}
  {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}

/-- A function that leaks nothing but the contract's public data may leak
more: its runs agree on fewer pairs of states. -/
theorem Verified.with_leak (h : Verified T c (sig.contract A pre post wa stack none))
    (f : Curry (sig.words A.ptrBits) (Mem → List Nat)) :
    Verified T c (sig.contract A pre post wa stack (some f)) :=
  h.of_implies ⟨fun _ hs => hs, fun _ _ _ q => q, fun s₁ s₂ _ _ hq => by
    dsimp only [Sig.contract] at hq ⊢
    split at hq
    · exact hq.elim
    · exact ⟨hq.1.1, hq.2⟩, h.2.2⟩

/-- A function that may leak `f` may leak `f'`, from which `f` follows. -/
theorem Verified.leak_mono {f f' : Curry (sig.words A.ptrBits) (Mem → List Nat)}
    (h : Verified T c (sig.contract A pre post wa stack (some f)))
    (hf : ∀ v₁ v₂ m₁ m₂, Curry.apply _ f' v₁ m₁ = Curry.apply _ f' v₂ m₂ →
      Curry.apply _ f v₁ m₁ = Curry.apply _ f v₂ m₂) :
    Verified T c (sig.contract A pre post wa stack (some f')) :=
  h.of_implies ⟨fun _ hs => hs, fun _ _ _ q => q, fun s₁ s₂ _ _ hq => by
    dsimp only [Sig.contract] at hq ⊢
    split at hq
    · exact hq.elim
    · exact ⟨⟨hq.1.1, hf _ _ _ _ hq.1.2⟩, hq.2⟩, h.2.2⟩
end

section
variable {name : String} {w : Bool} {N : Nat} {rest : List (String × Param)} {ret : Option IntTy}
  {post : (firstArraySigB name w .u64 N rest ret).Post 64} {wa : Bool} {stack : Nat}

/-- A proof that leaks `leak₁` (none: nothing) moved to a contract that leaks
`flagLeak` first (`Verified.with_leak`, `Verified.leak_mono`). -/
theorem Verified.leak_flag {c : Prog isa}
    {pre : Curry ((firstArraySigB name w .u64 N rest ret).words 64) (Mem → Prop)}
    {leak₁ : Option (Curry ((firstArraySigB name w .u64 N rest ret).words 64) (Mem → List Nat))}
    {leak : Curry ((firstArraySigB name w .u64 N rest ret).words 64) (Mem → List Nat)}
    (h : Verified target c ((firstArraySigB name w .u64 N rest ret).contract abi pre post wa stack leak₁))
    (hleak : ∀ ctx, Curry.Forall₂ (fun f g => ∀ m, f m = flagLeak m ctx :: g m) _
      (leak ctx) ((leak₁.getD (Curry.const (fun _ => []) _)) ctx)) :
    Verified target c ((firstArraySigB name w .u64 N rest ret).contract abi pre post wa stack (some leak)) := by
  cases leak₁ with
  | none => exact Verified.with_leak h leak
  | some l =>
    refine Verified.leak_mono h fun v₁ v₂ m₁ m₂ e => ?_
    cases v₁ with
    | nil =>
      cases v₂ with
      | nil =>
        have a := (hleak 0).apply [] m₁
        have b := (hleak 0).apply [] m₂
        exact (List.cons.inj (a.symm.trans (e.trans b))).2
      | cons p vs =>
        have a := (hleak 0).apply [] m₁
        have b := (hleak p).apply vs m₂
        exact (List.cons.inj (a.symm.trans (e.trans b))).2
    | cons p vs =>
      cases v₂ with
      | nil =>
        have a := (hleak p).apply vs m₁
        have b := (hleak 0).apply [] m₂
        exact (List.cons.inj (a.symm.trans (e.trans b))).2
      | cons p' vs' =>
        have a := (hleak p).apply vs m₁
        have b := (hleak p').apply vs' m₂
        exact (List.cons.inj (a.symm.trans (e.trans b))).2

end

/-- `onFlag` writes `rsp` nowhere if neither branch does (`Artifact.spSafe`). -/
theorem onFlag_spSafe {t : Nat} {c₁ c₂ : Prog isa}
    (h₁ : c₁.all (fun i => !isa.writesSp i) = true) (h₂ : c₂.all (fun i => !isa.writesSp i) = true) :
    (Impl.Gcm.X86_64.Flag.onFlag t c₁ c₂).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.Gcm.X86_64.Flag.onFlag, Code.iteCold, Code.all, h₁, h₂, Bool.and_true]
  rfl

end VG.X86_64
