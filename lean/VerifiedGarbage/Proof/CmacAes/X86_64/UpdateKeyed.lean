module

public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
import VerifiedGarbage.Proof.CmacAes.X86_64.KeyedLit
meta import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.CmacAes.X86_64.KeyedLit
meta import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
public import VerifiedGarbage.Impl.CmacAes.X86_64.Keyed
import VerifiedGarbage.Proof.Aes.X86_64.Sse.Ctr
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.X86_64.Ctr32

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` over the bitsliced AES, keys once

`vg_aes_ctr32_keys` (`Impl.CmacAes.X86_64.keys`) is `vg_aes_ctr32`'s
prologue and key loop, and leaves the bitsliced round keys in the scratch
buffer (`keysX86_64`, `KeysIn`); `vg_aes_ctr32_keyed`
(`Impl.CmacAes.X86_64.ctr32K`) is `vg_aes_ctr32` from them, without its key
loop, and leaves them as they are (`ctr32KX86_64`). Both proofs are
`vg_aes_ctr32`'s, the key setup's (`keys_ok`) and the batches' (`loop_ok`); their contracts are only their caller's: they are internal
functions.

`updateK` bitslices the keys once and chains the blocks by calls of
`vg_aes_ctr32_keyed`. Its proof is `update`'s (`UpdateLoop.lean`,
`UpdateCorrect.lean`, `Verified.lean`) with one more invariant, that the keys
stay in the working space (`KInv`): `chainIn` writes only the counter block
and the state, and `vg_aes_ctr32_keyed` leaves them. It is proven against
`updateX86_64` and `updateX86_64S` (`updateK_correct`, `updateKS_correct`,
`updateK_ct`, `updateKS_ct`), as the implementation `UpdateImpl.keyed`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Aes.X86_64 VG.Proof.Aes.X86_64 VG.Impl.CmacAes.X86_64

/-- The round keys of the `R`-round schedule `w` in slices, and the masks, in
the scratch buffer `b`, as `Impl.Aes.X86_64.Sse.keys` leaves them. -/
abbrev KeysIn (m : Mem) (b : Addr) (R : Nat) (w : List Byte) : Prop := Sse.Ready b R w m [] [⟨b, 1480⟩]

theorem keysAt_frame {m m' : Mem} {b : Addr} {R : Nat} {w : List Byte} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 144, 1232⟩ r) (h : KeysIn m b R w) : KeysIn m' b R w :=
  h.frame hf fun r hr => ⟨(hd r hr).sub_left fun x hx => by
      simp only [Region.Contains, Impl.Aes.X86_64.Sse.keysOff] at hx ⊢
      bv_omega, (hd r hr).sub_left (Region.sub_prefix (by decide))⟩

/-- The key schedule at `p` for `R` rounds, as bytes. -/
abbrev schedAt (m : Mem) (p : Addr) (R : Nat) : List Byte := Spec.Aes.bytesAt m p (16 * (R + 1))

/-- `vg_aes_ctr32_keys(schedule = rdi, rounds = rsi, scratch = r9)`: bitslices
the round keys of the schedule at `schedule` into the first 1472 bytes of
`scratch`. The code may read `schedule` (240 bytes) and read and write
`scratch` (1480 bytes); they may not overlap each other, and `scratch` may
not overlap the return address. The pointers and `rounds` are public. -/
def keysX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let scratch : Region := ⟨s.gpr .r9, 1480⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [scratch] ∧ sched.Disjoint scratch ∧ ret.Disjoint scratch ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' := KeysIn s'.mem (s.gpr .r9) (s.gpr .rsi).toNat (schedAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_aes_ctr32_keyed`: `Proof.Aes.ctr32X86_64S`, from the round keys of the
schedule at `schedule` bitsliced into `scratch` (`KeysIn`), which it leaves
there. -/
def ctr32KX86_64 : Contract isa where
  pre s := Proof.Aes.ctr32X86_64S.pre s ∧
    KeysIn s.mem (s.gpr .r9) (s.gpr .rsi).toNat (schedAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  post s s' := Proof.Aes.ctr32X86_64.post s s' ∧
    KeysIn s'.mem (s.gpr .r9) (s.gpr .rsi).toNat (schedAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub := Proof.Aes.ctr32X86_64.pub

/-! ## `vg_aes_ctr32_keys` -/

theorem keys_wp {s₀ : State} (hp : keysX86_64.pre s₀) :
    WP isa keys s₀ fun s' => gprPreserved s₀ s' ∧ keysX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dSS, dRS, hR⟩ := hp
  refine WP.mono (Sse.keys_ok (b := s₀.gpr .r9) (sch := s₀.gpr .rdi) (nr := (s₀.gpr .rsi).toNat)
    ⟨rfl, rfl, by simp, hR, .inr (by rw [hwr]; simp), by rw [hrd]; simp, dSS⟩) fun s' h => ⟨⟨fun r hr => h.gpr r ?_ ?_ ?_, ?_⟩, ?_⟩
  any_goals
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact h.frame.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact dRS) (by decide)
  · exact { h.ready with sc := .inr (by simp) }

/-! ## `vg_aes_ctr32_keyed` -/

theorem ctr32K_wp {s₀ : State} (hp₀ : ctr32KX86_64.pre s₀) :
    WP isa ctr32K s₀ fun s' => gprPreserved s₀ s' ∧ ctr32KX86_64.post s₀ s' := by
  obtain ⟨hpS, hkeys⟩ := hp₀
  have hp : CPre false s₀ := CPre.ofS hpS
  have hlp := hp.lp
  have hn := hlp.n16
  refine WP.seq (WP.mono (entry_ok false s₀) fun s1 ⟨r11, g1, m1, rd1, wr1, z1⟩ => ?_)
  refine WP.ite (s₀.gpr .r8 == 0) (by simp [X86_64.eval, z1]) (fun h0 => ?_) (fun h0 => ?_)
  · have h0 : (s₀.gpr .r8).toNat = 0 := by rw [eq_of_beq h0]; rfl
    have := hp.post (s' := s1) (fun x hx => g1 x hx.2.2.2.2.2) (by rw [m1]; exact Frame.refl _ _) (by rw [m1, h0]; rfl)
      (by rw [m1]; intro i hi; omega)
    exact WP.block_nil ⟨this.1, this.2, by rw [m1]; exact hkeys⟩
  have h0 : (s₀.gpr .r8).toNat ≠ 0 := fun h => by
    rw [beq_eq_false_iff_ne] at h0
    exact h0 (BitVec.eq_of_toNat_eq h)
  refine WP.mono (Proof.Aes.X86_64.loop_ok (nr := (s₀.gpr .rsi).toNat) (icb := Spec.Gcm.blockAt s₀.mem (s₀.gpr .rdx)) (w := schedAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
    hlp h0 (s := s1) ?_) fun s3 h3 => ?_
  · refine ⟨?_, ?_, ?_, ?_, fun x hx => g1 x hx.2.2.2.2.2, rd1, wr1, by rw [m1]; exact Frame.refl _ _, by rw [m1]; rfl,
      by rw [m1]; exact Proof.Aes.Memory.Processed.refl _ _ _ _⟩
    · rw [m1]; exact { hkeys with sc := by rw [wr1]; exact hp.hwS }
    · rw [g1 _ (by decide)]; simp
    · rw [r11]; simp
    · rw [g1 _ (by decide)]; simp
  · have := hp.post h3.gpr h3.frame h3.ctr h3.done
    exact ⟨this.1, this.2, { h3.ready with sc := .inr (by simp) }⟩

/-! ## The contracts, and constant time -/

theorem keys_correct (s : State) (hs : keysX86_64.pre s) :
    ∃ t s', Exec isa keys s t s' ∧ abiPreserved s s' ∧ keysX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := keys_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem ctr32K_correct (s : State) (hs : ctr32KX86_64.pre s) :
    ∃ t s', Exec isa ctr32K s t s' ∧ abiPreserved s s' ∧ ctr32KX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := ctr32K_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- Only the pointers and `rounds` reach an address or a branch. -/
theorem keys_ct : ConstantTime isa keysX86_64.pre keysX86_64.pub keys := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .r9]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

/-- Only the pointers, `rounds` and `n` reach an address or a branch. -/
theorem ctr32K_ct : ConstantTime isa ctr32KX86_64.pre ctr32KX86_64.pub ctr32K := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption


open VG VG.X86_64 VG.Impl.CmacAes.X86_64

/-! ## The keyed calls -/

theorem keys_nosp : NoSp keys := fun i hi => by
  have h : ((instrs keys).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  simpa using List.all_eq_true.mp h i hi

theorem ctr32K_nosp : NoSp ctr32K := fun i hi => by
  have h : ((instrs ctr32K).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  simpa using List.all_eq_true.mp h i hi

theorem keys_depth : keys.depth = 0 := by lit_decide
theorem ctr32K_depth : ctr32K.depth = 0 := by lit_decide

/-- The bitsliced keys in the scratch buffer through the write of the return
address of a call. -/
theorem keysIn_callEntry {s : State} {A : Addr} {R : Nat} {w : List Byte}
    (h : (below (s.gpr .rsp) 8).Disjoint ⟨A, 1480⟩) (hk : KeysIn s.mem A R w) : KeysIn s.callEntry.mem A R w :=
  keysAt_frame (callEntry_frame s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.sub_right (Sse.sub_scratch _ (by decide))).symm) hk

/-- The key schedule through the write of the return address of a call. -/
theorem sched_callEntry {s : State} {W : Addr} {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h : (below (s.gpr .rsp) 8).Disjoint ⟨W, 240⟩) : schedAt s.callEntry.mem W R = schedAt s.mem W R := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  exact bytesAt_frame (callEntry_frame s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.sub_right (Region.sub_prefix hRb)).symm) (by omega_using [hRb])

/-- `vg_aes_ctr32_keyed`'s precondition, on entry to a call with the regions
it is given. -/
theorem ctrK_pre {s : State} {W C D A : Addr} {R : Nat} (h : CallPreS s W C D A R) (h9 : s.gpr .r9 = A)
    (hk : KeysIn s.mem A R (schedAt s.mem W R)) :
    ctr32KX86_64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨A, 1480⟩]) := by
  have hR := toNat_rounds h.rounds
  have hR14 : R ≤ 14 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  refine ⟨h.ctr_pre h9, ?_⟩
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h9, hR,
    sched_callEntry h.rounds h.stkW]
  exact keysIn_callEntry h.stkS hk

/-- A call of `vg_aes_ctr32_keyed` itself, with its 1480 bytes of working
space at `A`, which hold the bitsliced keys. -/
theorem ctrK_callS {s : State} {W C D A : Addr} {R : Nat} (h : CallPreS s W C D A R) (h9 : s.gpr .r9 = A)
    (hk : KeysIn s.mem A R (schedAt s.mem W R)) :
    WP isa (.call ctrK.name ctrK.code) s fun s' =>
      CallPostX s W C D R ⟨A, 1480⟩ s' ∧ KeysIn s'.mem A R (schedAt s.mem W R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := ctr32KX86_64) ctr32K_correct ctr32K_nosp (by rw [ctr32K_depth]; decide)
    (rd := [⟨W, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16⟩, ⟨A, 1480⟩]) (ctrK_pre h h9 hk) h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [ctr32K_depth] at hf
  obtain ⟨hpc, hpk⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h9, hR,
    sched_callEntry h.rounds h.stkW, hm₂] at hpk
  refine ⟨⟨hrd, hwr, hcs, by simpa using hf, ?_⟩, hpk⟩
  rw [← hm₂]; exact h.toF.out hpc

/-- Calls of `vg_aes_ctr32_keyed` with the same arguments leak the same. -/
theorem ctrK_relS {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D A : Addr, ∃ R : Nat,
      (CallPreS s₁ W C D A R ∧ s₁.gpr .r9 = A ∧ KeysIn s₁.mem A R (schedAt s₁.mem W R)) ∧
      (CallPreS s₂ W C D A R ∧ s₂.gpr .r9 = A ∧ KeysIn s₂.mem A R (schedAt s₂.mem W R)) ∧
      s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call ctrK.name ctrK.code) fun _ _ => True := by
  refine RelCT.callEx ctr32K_correct ctr32K_ct fun s₁ s₂ hp => ?_
  obtain ⟨W, C, D, A, R, ⟨h₁, e₁, k₁⟩, ⟨h₂, e₂, k₂⟩, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, ctrK_pre h₁ e₁ k₁, ctrK_pre h₂ e₂ k₂, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [ctr32KX86_64, Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, e₁, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, e₂, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- … through `ctrCall`. -/
theorem ctrK_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R : Nat,
      (CallPreS s₁ W C D (S + BitVec.ofNat 64 512) R ∧ s₁.gpr .r9 = S ∧
        KeysIn s₁.mem (S + BitVec.ofNat 64 512) R (schedAt s₁.mem W R)) ∧
      (CallPreS s₂ W C D (S + BitVec.ofNat 64 512) R ∧ s₂.gpr .r9 = S ∧
        KeysIn s₂.mem (S + BitVec.ofNat 64 512) R (schedAt s₂.mem W R)) ∧
      s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (ctrCall ctrK) fun _ _ => True := by
  rw [ctrCall_512 rfl]
  refine (scrAdd_rel .r9).seq (ctrK_relS fun t₁ t₂ ⟨s₁, s₂, hp, a₁, a₂⟩ => ?_)
  obtain ⟨W, C, D, S, R, ⟨h₁, e₁, k₁⟩, ⟨h₂, e₂, k₂⟩, hsp⟩ := h s₁ s₂ hp
  exact ⟨W, C, D, _, R, ⟨h₁.scrAdd a₁, by rw [a₁.1, e₁], by rw [a₁.2.2.1]; exact k₁⟩,
    ⟨h₂.scrAdd a₂, by rw [a₂.1, e₂], by rw [a₂.2.2.1]; exact k₂⟩,
    by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), hsp]⟩

/-- The call, from the arguments `ctrArgs` leaves: the working space 512
bytes into the scratch buffer `S`. -/
theorem ctrK_ok {s : State} {W C D S : Addr} {R : Nat}
    (h : CallPreS s W C D (S + BitVec.ofNat 64 512) R) (h9 : s.gpr .r9 = S)
    (hk : KeysIn s.mem (S + BitVec.ofNat 64 512) R (schedAt s.mem W R)) :
    WP isa (ctrCall ctrK) s fun s' => CallPostX s W C D R ⟨S + BitVec.ofNat 64 512, 1480⟩ s' ∧
      KeysIn s'.mem (S + BitVec.ofNat 64 512) R (schedAt s.mem W R) := by
  rw [ctrCall_512 rfl]
  obtain ⟨s₁, run₁, a⟩ := scrAdd_ok .r9 s
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have m₁ : s₁.mem = s.mem := a.2.2.1
  refine WP.mono (ctrK_callS (h.scrAdd a) (by rw [a.1, h9]) (by rw [m₁]; exact hk)) fun _ ⟨h₂, k₂⟩ =>
    ⟨h₂.scrAdd a, by rw [m₁] at k₂; exact k₂⟩

/-! ## The loop, with the keys in place -/

/-- The working space of the keyed functions, 512 bytes into the scratch
buffer. -/
abbrev kb (s₀ : State) : Addr := S s₀ + BitVec.ofNat 64 512
abbrev kx (s₀ : State) : Region := ⟨kb s₀, 1480⟩

/-- The key schedule, as bytes. -/
abbrev ks (s₀ : State) : List Byte := schedAt s₀.mem (W s₀) (R s₀)

/-- The loop invariant, with the bitsliced keys in the working space. -/
def KInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  LInv s₀ (kx s₀) k s ∧ KeysIn s.mem (kb s₀) (R s₀) (ks s₀)

/-- The keys' region, in the working space. -/
theorem keys_sub (s₀ : State) : Region.Sub ⟨kb s₀ + BitVec.ofNat 64 144, 1232⟩ (kx s₀) :=
  Sse.sub_scratch _ (by decide)

theorem kx_counter (s₀ : State) : Region.Disjoint (kx s₀) ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ := by
  rw [show kx s₀ = ⟨S s₀ + BitVec.ofNat 64 512, 1480⟩ from rfl]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem keysArgs_ok (s : State) :
    ∃ s', runBlock isa keysArgs s = some s' ∧ s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .r9 = s.gpr .r15 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [keysArgs, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.map_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags]
  refine ⟨by simp, by simp, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial, trivial⟩
  simp [show BitVec.signExtend 64 (BitVec.ofNat 32 512) = BitVec.ofNat 64 512 by decide]

theorem UPre.kSub {s₀ : State} {Z : Region} (hZ : Z.Contains (kb s₀) 1480) : Region.Sub (kx s₀) Z :=
  sub_of_contains hZ

section
variable {s₀ : State} {Z : Region} (hp : UPre s₀ Z) (hZ : Z.Contains (kb s₀) 1480)
include hp hZ

/-- What the working space is apart from, at a call. -/
theorem UPre.kScr {s : State} (rsp : s.gpr .rsp = s₀.gpr .rsp) (wr : s.wr = s₀.wr) :
    ScrPre s (W s₀) (St s₀) (kx s₀) :=
  have z := hp.scrPre rsp wr
  have hs := UPre.kSub hZ
  ⟨z.w.sub_right hs, z.d.sub_right hs, z.stk.sub_right hs,
    Covers.trans (Covers.one ⟨Z, List.mem_singleton_self _, hZ⟩) z.wr⟩

theorem body_okK {k : Nat} (hk : k < N s₀) {s : State} (h : KInv s₀ k s) :
    WP isa (body ctrK) s fun s' => KInv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  obtain ⟨h, kk⟩ := h
  have h16k : 16 * k + 16 ≤ 16 * N s₀ := by omega_using [hk]
  have hdw := hp.data_wrap
  have hX := UPre.kSub hZ
  refine WP.seq (WP.mono (bodyA_wp hp hk h) fun s₁ ⟨pre, cs₁, mem₁, rd₁, wr₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ .rsp (by simp [calleeSaved]), h.rsp]
  have z := UPre.kScr hp hZ rsp₁ (by rw [wr₁, h.wr])
  have hS : CallPreS s₁ (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (kb s₀) (R s₀) :=
    pre.small z.w (kx_counter s₀).symm z.d z.stk z.wr
  have cZ : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ Z := hp.cSub (by decide) (by decide)
  have bigS := hp.big_of hX h.frame
  have f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, ⟨St s₀, 16⟩] s.mem s₁.mem := by
    rw [mem₁]; exact chainMem_frame _ _ _ _
  have big₁ : Frame (Big s₀ Z) s₀.mem s₁.mem := bigS.trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Z, by simp, cZ⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  have hR14 : R s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have kd : ∀ r ∈ [(⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region), stR s₀],
      Region.Disjoint ⟨kb s₀ + BitVec.ofNat 64 144, 1232⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (kx_counter s₀).sub_left (keys_sub s₀)
    · exact (hp.st_scr.sub_right hX).symm.sub_left (keys_sub s₀)
  have k₁ : KeysIn s₁.mem (kb s₀) (R s₀) (schedAt s₁.mem (W s₀) (R s₀)) := by
    rw [show schedAt s₁.mem (W s₀) (R s₀) = ks s₀ from UPre.sched_bytes hp big₁]
    exact keysAt_frame f₁ kd kk
  refine WP.seq (WP.mono (ctrK_ok hS pre.r9 k₁) fun s₂ ⟨h₂, k₂⟩ => ?_)
  obtain ⟨s₃, run₃, r13₃, r14₃, zf₃, keep₃, mem₃, rd₃, wr₃⟩ := advance_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₃.gpr r = s.gpr r := by
    rw [keep₃ r h13 h14, h₂.saved r hr, cs₁ r hr]
  have r13₂ : s₂.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [h₂.saved .r13 (by simp [calleeSaved]), cs₁ .r13 (by simp [calleeSaved]), h.r13]
  have r14₂ : s₂.gpr .r14 = BitVec.ofNat 64 (N s₀ - k) := by
    rw [h₂.saved .r14 (by simp [calleeSaved]), cs₁ .r14 (by simp [calleeSaved]), h.r14]
  have hN := (s₀.gpr .r8).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_using [hk])]; rfl
  have cst : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (stR s₀) :=
    hp.st_scr.symm.sub_left cZ
  have cq : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left cZ).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, mem₁, chainMem_counter _ cst cq, h.state,
    UPre.block_bytes hp bigS hk] at out
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [r13₃, r13₂, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega_using [])]
  · rw [r14₃, r14₂, dec]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₃, h₂.rd, rd₁, h.rd]
  · rw [wr₃, h₂.wr, wr₁, h.wr]
  · rw [mem₃]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨kx s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  · rw [mem₃, out, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [mem₃]
    rw [show schedAt s₁.mem (W s₀) (R s₀) = ks s₀ from UPre.sched_bytes hp big₁] at k₂
    exact k₂
  · rw [zf₃, r14₂, dec]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdw])] at this
      simpa using this
    · intro he; rw [he]; rfl

theorem loop_okK {k : Nat} (hk : k < N s₀) {s : State} (h : KInv s₀ k s) :
    WP isa (.loop (body ctrK) .ne) s (KInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body ctrK) (c := .ne) (Q := KInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ KInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_okK hp hZ hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz]]
  · right
    refine ⟨by simp [X86_64.eval, zf', hz], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz], h'⟩

/-- After `keysArgs`: the loop's invariant before its first block, and the
arguments of `vg_aes_ctr32_keys`. -/
structure KA (s₀ s : State) : Prop where
  inv : LInv s₀ (kx s₀) 0 s
  rdi : s.gpr .rdi = W s₀
  rsi : s.gpr .rsi = BitVec.ofNat 64 (R s₀)
  r9 : s.gpr .r9 = kb s₀

omit hp hZ in
theorem keysArgs_wp {s : State} (h : LInv s₀ (kx s₀) 0 s) : WP isa (.block keysArgs) s (KA s₀) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, r9₁, o₁, m₁, rd₁, wr₁⟩ := keysArgs_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) : s₁.gpr r = s.gpr r :=
    o₁ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₁, h.rd], by rw [wr₁, h.wr], by rw [m₁]; exact h.frame,
    by rw [m₁]; exact h.state⟩, by rw [rdi₁, h.rbx], by rw [rsi₁, h.rbp, rsi_ofNat], by rw [r9₁, h.r15]⟩
  · rw [g .rbx (by simp [calleeSaved]), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]), h.r12]
  · rw [g .r13 (by simp [calleeSaved]), h.r13]
  · rw [g .r14 (by simp [calleeSaved]), h.r14]
  · rw [g .r15 (by simp [calleeSaved]), h.r15]
  · rw [g .rsp (by simp [calleeSaved]), h.rsp]

omit hZ in
theorem KA.regs {s₁ : State} (h : KA s₀ s₁) : s₁.rd ++ s₁.wr = [schR s₀, dataR s₀, stR s₀, Z] := by
  rw [h.inv.rd, h.inv.wr, hp.rd, hp.wr]; rfl

theorem KA.pre {s₁ : State} (h : KA s₀ s₁) :
    keysX86_64.pre (s₁.callEntry.withRegions [⟨W s₀, 240⟩] [kx s₀]) := by
  have hX := UPre.kSub hZ
  have hR := toNat_rounds hp.rounds
  simp only [keysX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr s₁ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s₁ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s₁ (by decide : Reg.r9 ≠ .rsp),
    h.r9, h.rdi, h.rsi, hR]
  exact ⟨trivial, trivial, hp.sch_scr.sub_right hX, by rw [h.inv.rsp]; exact hp.stk_scr.sub_right hX,
    hp.rounds⟩

theorem KA.reads {s₁ : State} (h : KA s₀ s₁) : Covers ([⟨W s₀, 240⟩] ++ [kx s₀]) (s₁.rd ++ s₁.wr) := by
  rw [KA.regs hp (Z := Z) h]
  exact Covers.cons (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
    (Covers.cons (Covers.one ⟨Z, by simp, hZ⟩) Covers.nil)

theorem KA.writes {s₁ : State} (h : KA s₀ s₁) : Covers [kx s₀] s₁.wr := by
  rw [h.inv.wr, hp.wr]; exact Covers.one ⟨Z, by simp, hZ⟩

/-- The call of `vg_aes_ctr32_keys`. -/
theorem keysOnly_wp {s₁ : State} (h : KA s₀ s₁) :
    WP isa (.call "vg_aes_ctr32_keys" keys) s₁ (KInv s₀ 0) := by
  have hX := UPre.kSub hZ
  have hR := toNat_rounds hp.rounds
  have hi := h.inv
  have big₁ : Frame (Big s₀ Z) s₀.mem s₁.mem := hp.big_of hX hi.frame
  refine WP.call (k := keysX86_64) keys_correct keys_nosp (by rw [keys_depth]; decide)
    (KA.pre hp hZ h) (KA.reads hp hZ h) (KA.writes hp hZ h) ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [keys_depth] at hf
  have hf' : Frame [kx s₀, stkR s₀] s₁.mem s'.mem := by
    have := hf; rw [hi.rsp] at this; simpa using this
  simp only [keysX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s₁ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s₁ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s₁ (by decide : Reg.r9 ≠ .rsp), h.r9, h.rdi, h.rsi, hR,
    sched_callEntry hp.rounds (by rw [hi.rsp]; exact hp.stk_sch), hm₂,
    show schedAt s₁.mem (W s₀) (R s₀) = ks s₀ from UPre.sched_bytes hp big₁] at hpost
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hrd, hi.rd], by rw [hwr, hi.wr], ?_, ?_⟩, hpost⟩
  · rw [hcs .rbx (by simp [calleeSaved]), hi.rbx]
  · rw [hcs .rbp (by simp [calleeSaved]), hi.rbp]
  · rw [hcs .r12 (by simp [calleeSaved]), hi.r12]
  · rw [hcs .r13 (by simp [calleeSaved]), hi.r13]
  · rw [hcs .r14 (by simp [calleeSaved]), hi.r14]
  · rw [hcs .r15 (by simp [calleeSaved]), hi.r15]
  · rw [hcs .rsp (by simp [calleeSaved]), hi.rsp]
  · exact hi.frame.trans (hf'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨kx s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  · rw [bytesAt_frame hf' (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_scr.sub_right hX
        · exact hp.stk_st.symm) (by decide), hi.state]

/-- The keys, bitsliced once before the loop. -/
theorem keysCall_wp {s : State} (h : LInv s₀ (kx s₀) 0 s) :
    WP isa (.seq (.block keysArgs) (.call "vg_aes_ctr32_keys" keys)) s (KInv s₀ 0) :=
  WP.seq (WP.mono (keysArgs_wp h) fun _ h₁ => keysOnly_wp hp hZ h₁)

theorem mid_wpK {s₁ : State} (h : LInv s₀ (kx s₀) 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block [])
      (.seq (.seq (.block keysArgs) (.call "vg_aes_ctr32_keys" keys)) (.loop (body ctrK) .ne))) s₁
      (LInv s₀ (kx s₀) (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := hz
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (keysCall_wp hp hZ h) fun _ hk =>
      WP.mono (loop_okK hp hZ (by omega_using [hn]) hk) fun _ h => h.1)

/-- `updateK`, with the part `Z` of the scratch buffer writable, which holds
the keyed functions' working space. -/
theorem updateK_wpG :
    WP isa updateK s₀ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' :=
  WP.seq (WP.mono (prologue_wp hp) fun _ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wpK hp hZ h₁ z₁) fun _ h₂ =>
      epilogue_wp hp (UPre.kSub hZ) (Offset.disjoint _ (by decide) (by decide) (by decide)).symm h₂))

end

/-! ## Constant time

As for `update` (`Verified.lean`): the taint analysis covers the code between
the calls, and each call is constant time by its own proof. -/

section CT

variable {s₀ : State} {Z : Region} (hp : UPre s₀ Z) (hZ : Z.Contains (kb s₀) 1480)

/-- Before the call of a block: `Mid`, and the keys. -/
def MK (s₀ : State) (k : Nat) (s : State) : Prop :=
  Mid s₀ k s ∧ KeysIn s.mem (kb s₀) (R s₀) (schedAt s.mem (W s₀) (R s₀))

include hp hZ in
theorem bodyMidK_wp {k : Nat} (hk : k < N s₀) {s : State} (h : KInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (MK s₀ k) := by
  obtain ⟨h, kk⟩ := h
  have hX := UPre.kSub hZ
  refine WP.mono (bodyA_wp hp hk h) fun s₁ hb => ⟨⟨hb.pre, by rw [hb.saved .r13 (by simp [calleeSaved]), h.r13],
      by rw [hb.saved .r14 (by simp [calleeSaved]), h.r14], by rw [hb.saved .rsp (by simp [calleeSaved]), h.rsp],
      by rw [hb.wr, h.wr]⟩, ?_⟩
  have cZ : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ Z := hp.cSub (by decide) (by decide)
  have f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, ⟨St s₀, 16⟩] s.mem s₁.mem := by
    rw [hb.mem]; exact chainMem_frame _ _ _ _
  have big₁ : Frame (Big s₀ Z) s₀.mem s₁.mem := (hp.big_of hX h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Z, by simp, cZ⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  have hR14 : R s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  rw [show schedAt s₁.mem (W s₀) (R s₀) = ks s₀ from UPre.sched_bytes hp big₁]
  refine keysAt_frame f₁ (fun r hr => ?_) kk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (kx_counter s₀).sub_left (keys_sub s₀)
  · exact (hp.st_scr.sub_right hX).symm.sub_left (keys_sub s₀)

include hp hZ in
/-- The arguments of the call, from `MK`. -/
theorem MK.callPre {k : Nat} {s : State} (h : MK s₀ k s) :
    CallPreS s (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (kb s₀) (R s₀) :=
  have z := UPre.kScr hp hZ h.1.rsp h.1.wr
  h.1.pre.small z.w (kx_counter s₀).symm z.d z.stk z.wr

variable {s₀' : State} {Z' : Region} (hp' : UPre s₀' Z') (hZ' : Z'.Contains (kb s₀') 1480)
  (hq : updateX86_64.pub s₀ s₀')

include hp hZ hp' hZ' hq in
theorem body_ctK (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ KInv s₀ k s₁ ∧ KInv s₀' k s₂) (body ctrK) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (chainIn ++ updArgs)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r13, .r14]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < N s₀ ∧ KInv s₀ k s₁ ∧ KInv s₀' k s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.2.1.1 h.2.2.1)) hA).wp
    (F₁ := MK s₀ k) (F₂ := MK s₀' k) fun _ _ h =>
      ⟨bodyMidK_wp hp hZ h.1 h.2.1, bodyMidK_wp hp' hZ' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (ctrK_rel (P := fun s₁ s₂ => MK s₀ k s₁ ∧ MK s₀' k s₂) fun s₁ s₂ h =>
      ⟨W s₀, S s₀ + BitVec.ofNat 64 2048, St s₀, S s₀, R s₀,
        ⟨MK.callPre hp hZ h.1, h.1.1.pre.r9, h.1.2⟩, by
          rw [pub_W hq, pub_S hq, pub_St hq, pub_R hq]
          exact ⟨MK.callPre hp' hZ' h.2, h.2.1.pre.r9, h.2.2⟩,
        by rw [h.1.1.rsp, h.2.1.rsp, pub_rsp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (ctrK_ok (MK.callPre hp hZ h.1) h.1.1.pre.r9 h.1.2) fun _ hc =>
        ⟨by rw [hc.1.saved .r13 (by simp [calleeSaved]), h.1.1.r13],
          by rw [hc.1.saved .r14 (by simp [calleeSaved]), h.1.1.r14]⟩,
       WP.mono (ctrK_ok (MK.callPre hp' hZ' h.2) h.2.1.pre.r9 h.2.2) fun _ hc =>
        ⟨by rw [hc.1.saved .r13 (by simp [calleeSaved]), h.2.1.r13],
          by rw [hc.1.saved .r14 (by simp [calleeSaved]), h.2.1.r14]⟩⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r13, h.2.r13, pub_Dp hq]
      · rw [h.1.r14, h.2.r14, pub_N hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-- The loop's relation, with the number of iterations left. -/
def KRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ KInv s₀ k s₁ ∧ KInv s₀' k s₂

include hp hZ hp' hZ' hq in
theorem loop_ctK (n : Nat) :
    RelCT isa (KRel s₀ s₀' n) (.loop (body ctrK) .ne)
      fun s₁ s₂ => KInv s₀ (N s₀) s₁ ∧ KInv s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (KRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : KRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (body_ctK hp hZ hp' hZ' hq k).wp
    (F₁ := fun (s' : State) => KInv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)))
    (F₂ := fun (s' : State) => KInv s₀' (k + 1) s' ∧ s'.zf = some (decide (N s₀' - (k + 1) = 0)))
    fun _ _ h => ⟨body_okK hp hZ h.1 h.2.1, body_okK hp' hZ' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hN] at z₂
  have e₁ : isa.eval .ne s₁ = some (!decide (N s₀ - (k + 1) = 0)) := by
    show s₁.zf.map _ = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some (!decide (N s₀ - (k + 1) = 0)) := by
    show s₂.zf.map _ = _; rw [z₂]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [h0], l₁, l₂⟩

include hp hZ hp' hZ' hq in
/-- The keys' call, with the same arguments in both runs. -/
theorem keysCall_rel :
    RelCT isa (fun s₁ s₂ => LInv s₀ (kx s₀) 0 s₁ ∧ LInv s₀' (kx s₀') 0 s₂)
      (.seq (.block keysArgs) (.call "vg_aes_ctr32_keys" keys))
      fun s₁ s₂ => KInv s₀ 0 s₁ ∧ KInv s₀' 0 s₂ := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block keysArgs) h).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => LInv s₀ (kx s₀) 0 s₁ ∧ LInv s₀' (kx s₀') 0 s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.1 h.2)) hA).wp
    (F₁ := KA s₀) (F₂ := KA s₀') fun _ _ h => ⟨keysArgs_wp h.1, keysArgs_wp h.2⟩
  have c := (RelCT.callEx (n := "vg_aes_ctr32_keys") keys_correct keys_ct
    (P := fun s₁ s₂ => KA s₀ s₁ ∧ KA s₀' s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, KA.pre hp hZ h.1, KA.pre hp' hZ' h.2, by
        simp only [keysX86_64, State.withRegions_gpr, State.callEntry_rsp,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp), h.1.rdi, h.1.rsi, h.1.r9, h.2.rdi, h.2.rsi,
          h.2.r9, h.1.inv.rsp, h.2.inv.rsp, pub_W hq, pub_R hq, kb, pub_S hq, pub_rsp hq]
        exact ⟨trivial, trivial, trivial, trivial⟩,
        KA.reads hp hZ h.1, KA.writes hp hZ h.1, KA.reads hp' hZ' h.2, KA.writes hp' hZ' h.2,
        by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩).wp
    (F₁ := KInv s₀ 0) (F₂ := KInv s₀' 0) fun _ _ h => ⟨keysOnly_wp hp hZ h.1, keysOnly_wp hp' hZ' h.2⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq (c.mono (fun _ _ h => h) fun _ _ h => h.2)

include hp hZ hp' hZ' hq in
theorem updateK_relG :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') updateK fun _ _ => True := by
  have hN := pub_N hq
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := fun (s : State) => LInv s₀ (kx s₀) 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv s₀' (kx s₀') 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv s₀ (kx s₀) 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' (kx s₀') 0 b ∧ b.zf = some (decide (N s₀' = 0)))) ∧ isa.eval .e a = some true) _
    (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (LInv s₀ (kx s₀) 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' (kx s₀') 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block [])
        (.seq (.seq (.block keysArgs) (.call "vg_aes_ctr32_keys" keys)) (.loop (body ctrK) .ne)))
      (fun a b => LInv s₀ (kx s₀) (N s₀) a ∧ LInv s₀' (kx s₀') (N s₀') b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, hN]
    · refine (nil.wp (F₁ := LInv s₀ (kx s₀) (N s₀)) (F₂ := LInv s₀' (kx s₀') (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · by_cases hn : N s₀ = 0
      · exact RelCT.of_false fun a b h => by
          have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simp [hn] at this
      · have kc := keysCall_rel hp hZ hp' hZ' hq
        exact ((kc.mono (fun a b h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h).seq
          ((loop_ctK hp hZ hp' hZ' hq (N s₀ - 0)).mono
            (fun a b h => ⟨0, rfl, by omega_using [hn], h.1, h.2⟩)
            fun _ _ h => ⟨h.1.1, h.2.1⟩)).mono (fun _ _ h => h) fun _ _ h => h
  have epi := RelCT.taint (A := taint)
    (P := fun a b => LInv s₀ (kx s₀) (N s₀) a ∧ LInv s₀' (kx s₀') (N s₀') b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r15, h.2.r15, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

end CT

/-! ## The contracts, and the implementation -/

/-- `updateX86_64`'s scratch buffer holds the keyed functions' working space. -/
theorem kx_full (s₀ : State) : (scrR s₀).Contains (kb s₀) 1480 :=
  Offset.contains_base _ (by decide) (by decide)

/-- … and so does `updateX86_64S`'s, its first 512 bytes left out. -/
theorem kx_small (s₀ : State) : (⟨S s₀ + BitVec.ofNat 64 512, 1664⟩ : Region).Contains (kb s₀) 1480 := by
  simp [Region.Contains]

theorem updateK_mx : updateK.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem updateK_nosp : NoSp updateK := fun i hi => by
  have h : ((instrs updateK).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  simpa using List.all_eq_true.mp h i hi

theorem updateK_correct (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa updateK s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpo⟩ := updateK_wpG (UPre.of hs) (kx_full s)
  exact ⟨t, s', he, abiPreserved_of_exec updateK_mx he hg, hpo⟩

theorem updateKS_correct (s : State) (hs : updateX86_64S.pre s) :
    ∃ t s', Exec isa updateK s t s' ∧ abiPreserved s s' ∧ updateX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hpo⟩ := updateK_wpG (UPre.ofS hs) (kx_small s)
  exact ⟨t, s', he, abiPreserved_of_exec updateK_mx he hg, hpo⟩

theorem updateK_ct : ConstantTime isa updateX86_64.pre updateX86_64.pub updateK :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (updateK_relG (UPre.of h₁) (kx_full _) (UPre.of h₂) (kx_full _) hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem updateKS_ct : ConstantTime isa updateX86_64S.pre updateX86_64S.pub updateK :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (updateK_relG (UPre.ofS h₁) (kx_small _) (UPre.ofS h₂) (kx_small _) hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The chaining over the bitsliced AES, its round keys bitsliced once
(`updateK`): `vg_cmac_aes_update`, which goes with `vg_aes_ctr32`. -/
def UpdateImpl.keyed : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update", updateK⟩
  depth := by lit_decide
  ok := updateK_correct
  ct := updateK_ct
  nosp := updateK_nosp
  mxcsr := updateK_mx
  spSafe := Code.all_of_spTest (by lit_decide)
  xdepth := by lit_decide
  suffix := ""
  features := []
  ctr := .scalar
  small := some ⟨updateKS_correct, updateKS_ct⟩
  level := .sse
  side := by lit_decide

end VG.Proof.CmacAes.X86_64
