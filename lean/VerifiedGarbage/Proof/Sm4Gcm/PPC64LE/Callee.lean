module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr32
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey

/-!
# SM4-GCM on PPC64LE: SM4's code, inlined

Untrusted: everything here is checked by Lean. SM4-GCM runs SM4's counter
mode (`Impl.Sm4.PPC64LE.ctr32`) and key expansion (`Impl.Sm4.PPC64LE.expandKey`)
inline, from their proofs against their own contracts, as AES-GCM calls
AES's (`Proof/AesGcm/PPC64LE/Callee.lean`): what the arguments in `r3`–`r7`
must be (`CtrCall`, `KeyCall`), and what the code leaves (`CtrPost`,
`KeyPost`): its postcondition, memory changed only in the buffers it writes,
and the nonvolatile registers and the link register kept. `CT.ctr` and
`CT.key`: such code, with the same public arguments in both runs, is
constant time.

`wp_inline` and `relCT_inline` run verified code that may call functions
but has no frames, narrowed to regions of its own (`WP.narrow`,
`trace_narrow`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE (CT Both)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32 inc32)

/-! ## Verified code, inline -/

/-- Running verified code without frames inline: as `WP.inline`, for code that
may call functions. -/
theorem wp_inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → Frame wr s.mem s'.mem →
      abiPreserved (s.withRegions rd wr) (s'.withRegions rd wr) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noFrames = true) : WP isa c s Q := by
  refine WP.narrow (P := fun s' => abiPreserved (s.withRegions rd wr) s' ∧ k.post (s.withRegions rd wr) s')
    ?_ hc hw (fun s' a b _ d e => hQ s' a b d e.1 e.2) hn
  obtain ⟨t, s', he, ha, hp⟩ := hv _ hpre
  exact ⟨t, s', he, ha, hp⟩

/-- Two runs of verified code without frames inline, narrowed in each run to
regions of its own where its precondition and public data hold, leak the
same. -/
theorem relCT_inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.withRegions rd wr) ∧ k.pre (s₂.withRegions rd wr) ∧
      k.pub (s₁.withRegions rd wr) (s₂.withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr ∧
      Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  obtain ⟨_, e₁'⟩ := trace_narrow hv p₁ c₁ w₁ e₁
  obtain ⟨_, e₂'⟩ := trace_narrow hv p₂ c₂ w₂ e₂
  exact ⟨hct _ _ _ _ _ _ p₁ p₂ hpub e₁' e₂', trivial⟩

theorem toNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## SM4's counter mode -/

/-- The bytes of SM4's working space. -/
abbrev sBytes : Nat := 3264

theorem scratch_bytes : 8 * (Impl.Sm4.PPC64LE.slots + 6) = sBytes := by
  rw [Proof.Sm4.PPC64LE.slots_eq]

theorem ctr32_noFrames : Impl.Sm4.PPC64LE.ctr32.noFrames = true := by lit_decide

/-- What SM4's counter mode `(schedule = r3, counter = r4, data = r5, n = r6,
scratch = r7)` needs. -/
structure CtrCall (s : State) (K C D S : Addr) (n : Nat) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = C
  r5 : s.gpr .r5 = D
  r6 : s.gpr .r6 = BitVec.ofNat 64 n
  r7 : s.gpr .r7 = S
  n_lt : n < 2 ^ 64
  kc : (⟨K, 128⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 128⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 128⟩ : Region).Disjoint ⟨S, sBytes⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, sBytes⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, sBytes⟩
  fK : K.toNat + 128 ≤ 2 ^ 64
  fC : C.toNat + 16 ≤ 2 ^ 64
  fD : D.toNat + 16 * n ≤ 2 ^ 64
  fS : S.toNat + sBytes ≤ 2 ^ 64
  reads : Covers ([⟨K, 128⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, sBytes⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, sBytes⟩] s.wr

/-- What SM4's counter mode leaves. -/
structure CtrPost (s : State) (K C D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, sBytes⟩] s.mem s'.mem
  out : blocksAt s'.mem D n =
    ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem K)) (blockAt s.mem C) (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat inc32 n (blockAt s.mem C)

theorem CtrCall.pre {s : State} {K C D S : Addr} {n : Nat} (h : CtrCall s K C D S n) :
    (Proof.Sm4.PPC64LE.modeContract 16 Proof.Sm4.PPC64LE.Modes.ctr32Post).pre
      (s.withRegions [⟨K, 128⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, sBytes⟩]) := by
  simp only [Proof.Sm4.PPC64LE.modeContract, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, h.r3, h.r4, h.r5, h.r6, h.r7, toNat64 h.n_lt, scratch_bytes]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.fK, h.fC, h.fD, h.fS⟩

theorem ctr_wp {s : State} {K C D S : Addr} {n : Nat} (h : CtrCall s K C D S n) :
    WP isa Impl.Sm4.PPC64LE.ctr32 s (CtrPost s K C D S n) := by
  refine wp_inline (k := Proof.Sm4.PPC64LE.modeContract 16 Proof.Sm4.PPC64LE.Modes.ctr32Post)
    Proof.Sm4.PPC64LE.Modes.ctr32_correct h.pre h.reads h.writes ?_ ctr32_noFrames
  intro s' hrd hwr hf ⟨hcs, hsp, hlr⟩ hpost
  simp only [State.withRegions_gpr, State.withRegions_sp] at hcs hsp
  refine ⟨hrd, hwr, hsp, hlr, hcs, hf, ?_, ?_⟩ <;>
  simp only [Proof.Sm4.PPC64LE.modeContract, Proof.Sm4.PPC64LE.Modes.ctr32Post, State.withRegions_gpr,
    State.withRegions_mem, h.r3, h.r4, h.r5, h.r6, toNat64 h.n_lt] at hpost
  exacts [hpost.1, hpost.2]

/-- SM4's counter mode with the same arguments in both runs is constant time. -/
theorem CT.ctr {I : State → Prop}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ K C D S : Addr, ∃ n : Nat,
      CtrCall s₁ K C D S n ∧ CtrCall s₂ K C D S n ∧ s₁.sp = s₂.sp) :
    CT I Impl.Sm4.PPC64LE.ctr32 := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr × Addr × Addr × Nat) (s₁ s₂ : State) =>
      CtrCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧ CtrCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧
        s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, C, D, S, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp.1 hp.2
      exact ⟨(K, C, D, S, n), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, C, D, S, n⟩ := x
  refine relCT_inline Proof.Sm4.PPC64LE.Modes.ctr32_correct Proof.Sm4.PPC64LE.Modes.ctr32_constantTime
    [⟨K, 128⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, sBytes⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Sm4.PPC64LE.modeContract, Proof.Sm4.PPC64LE.modePub, State.withRegions_gpr, State.withRegions_sp, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₂.r3,
    h₂.r4, h₂.r5, h₂.r6, h₂.r7, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## SM4's key expansion -/

/-- The bytes of key expansion's working space. -/
abbrev kBytes : Nat := 3216

theorem key_bytes : 8 * Impl.Sm4.PPC64LE.slots = kBytes := by
  rw [Proof.Sm4.PPC64LE.slots_eq]

theorem expandKey_noFrames : Impl.Sm4.PPC64LE.expandKey.noFrames = true := by lit_decide

/-- What SM4's key expansion `(key = r3, schedule = r4, scratch = r5)` needs. -/
structure KeyCall (s : State) (K C S : Addr) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = C
  r5 : s.gpr .r5 = S
  kc : (⟨K, 16⟩ : Region).Disjoint ⟨C, 128⟩
  ks : (⟨K, 16⟩ : Region).Disjoint ⟨S, kBytes⟩
  cs : (⟨C, 128⟩ : Region).Disjoint ⟨S, kBytes⟩
  fK : K.toNat + 16 ≤ 2 ^ 64
  fC : C.toNat + 128 ≤ 2 ^ 64
  fS : S.toNat + kBytes ≤ 2 ^ 64
  reads : Covers ([⟨K, 16⟩] ++ [⟨C, 128⟩, ⟨S, kBytes⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 128⟩, ⟨S, kBytes⟩] s.wr

/-- What SM4's key expansion leaves. -/
structure KeyPost (s : State) (K C S : Addr) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 128⟩, ⟨S, kBytes⟩] s.mem s'.mem
  out : Spec.Sm4.scheduleAt s'.mem C = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem K)

theorem KeyCall.pre {s : State} {K C S : Addr} (h : KeyCall s K C S) :
    Proof.Sm4.expandKeyPPC64LE.pre (s.withRegions [⟨K, 16⟩] [⟨C, 128⟩, ⟨S, kBytes⟩]) := by
  simp only [Proof.Sm4.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, h.r3, h.r4, h.r5, key_bytes]
  exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.fK, h.fC, h.fS⟩

theorem key_wp {s : State} {K C S : Addr} (h : KeyCall s K C S) :
    WP isa Impl.Sm4.PPC64LE.expandKey s (KeyPost s K C S) := by
  refine wp_inline (k := Proof.Sm4.expandKeyPPC64LE) Proof.Sm4.PPC64LE.expandKey_correct h.pre h.reads
    h.writes ?_ expandKey_noFrames
  intro s' hrd hwr hf ⟨hcs, hsp, hlr⟩ hpost
  simp only [State.withRegions_gpr, State.withRegions_sp] at hcs hsp
  refine ⟨hrd, hwr, hsp, hlr, hcs, hf, ?_⟩
  simp only [Proof.Sm4.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_mem, h.r3, h.r4] at hpost
  exact hpost

/-- SM4's key expansion with the same arguments in both runs is constant time. -/
theorem CT.key {I : State → Prop}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ K C S : Addr, KeyCall s₁ K C S ∧ KeyCall s₂ K C S ∧ s₁.sp = s₂.sp) :
    CT I Impl.Sm4.PPC64LE.expandKey := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr × Addr) (s₁ s₂ : State) =>
      KeyCall s₁ x.1 x.2.1 x.2.2 ∧ KeyCall s₂ x.1 x.2.1 x.2.2 ∧ s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, C, S, h₁, h₂, hsp⟩ := h s₁ s₂ hp.1 hp.2
      exact ⟨(K, C, S), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, C, S⟩ := x
  refine relCT_inline Proof.Sm4.PPC64LE.expandKey_correct Proof.Sm4.PPC64LE.expandKey_ct [⟨K, 16⟩]
    [⟨C, 128⟩, ⟨S, kBytes⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Sm4.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_sp, h₁.r3, h₁.r4, h₁.r5,
    h₂.r3, h₂.r4, h₂.r5, hsp]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.Sm4Gcm.PPC64LE
