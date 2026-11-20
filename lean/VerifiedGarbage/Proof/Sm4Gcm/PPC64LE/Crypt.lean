module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyVerified
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr32
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr32
public import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey

/-! ### `Sm4Gcm.PPC64LE.Callee`, which this module and modules that import it used -/

section

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

end

end

/-!
# SM4-GCM on PPC64LE: counter mode over a piece (`crypt`)

Untrusted: everything here is checked by Lean. AES-GCM's `crypt`
(`Proof/AesGcm/PPC64LE/Crypt.lean`, `CryptOk.lean`) with SM4's counter mode
inlined (`CtrCall`), from the schedule in the context, with its working
space `X` of 3264 bytes at `r28`: `XOk` says it fits and lies apart from
the context, the state and `W`, and the pieces cover it with
the permission to write it (`xw`) and keep the data apart from it (`dx`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE VG.WriteBytes
open VG.Impl.AesGcm.PPC64LE (mov cryptHead cryptFill splitWhole xorLoop)
open VG.Proof.AesGcm.PPC64LE (Env Lay Keeps Keeps' DataW DataOk covers_left covers_prefix add_ofNat_assoc
  bytesAt_frame blockAt_frame eval_zero split_ok minLen_ok xorLoop_ok LoopPre ofNat_sub64 split_disj
  done_append toNat64 length_xorBytes xorBytes bytesAt_add bytesAt_writeBytes_self writeBytes_frame' write_8
  zeroT_bytes blocksAt_one length_bytesAt)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)

/-! ## SM4's working space -/

/-- SM4's working space, at `x` (held in `r28`). -/
abbrev xR (x : Addr) : Region := ⟨x, sBytes⟩

/-- SM4's working space fits, and is apart from the context, the state and
AES-GCM's working space `W`. -/
structure XOk (c st w x : Addr) : Prop where
  fit : x.toNat + sBytes ≤ 2 ^ 64
  cx : (⟨c, 256⟩ : Region).Disjoint (xR x)
  sx : (⟨st, 80⟩ : Region).Disjoint (xR x)
  wx : (⟨w, 288⟩ : Region).Disjoint (xR x)

/-- The cipher of the key schedule at `C`. -/
abbrev ciphOf (m : Mem) (C : Addr) : Block → Block :=
  Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt m C)

theorem ciph_frame {c : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨c, 256⟩ : Region).Disjoint r) : ciphOf m' c = ciphOf m c := by
  simp only [ciphOf]
  rw [Proof.Sm4.scheduleAt_frame hf fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide))]

/-- The regions `crypt` writes. -/
abbrev crFrame (st x D : Addr) (n : Nat) : List Region :=
  [⟨D, n⟩, ⟨st + BitVec.ofNat 64 48, 32⟩, xR x]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go. -/
structure CrIn (V : Reg → BitVec 64) (sp : Addr) (icb : Block) (P : Nat) (D : Addr) (n : Nat)
    (s : State) : Prop where
  env : Env V sp s
  r24 : s.gpr .r24 = D
  r25 : s.gpr .r25 = BitVec.ofNat 64 n
  r26 : s.gpr .r26 = BitVec.ofNat 64 (P % 16)
  data : DataW (V .r29) (V .r30) (V .r31) s D n
  xw : Covers [xR (V .r28)] s.wr
  dx : (⟨D, n⟩ : Region).Disjoint (xR (V .r28))

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (V : Reg → BitVec 64) (sp : Addr) (icb : Block) (P : Nat) (D : Addr) (n : Nat)
    (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env V sp s
  le : j ≤ n
  r24 : s.gpr .r24 = D + BitVec.ofNat 64 j
  r25 : s.gpr .r25 = BitVec.ofNat 64 (n - j)
  data : DataW (V .r29) (V .r30) (V .r31) s D n
  xw : Covers [xR (V .r28)] s.wr
  dx : (⟨D, n⟩ : Region).Disjoint (xR (V .r28))
  ctr : Ctr m₀ (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) (ciphOf m₀ (V .r29)) icb P →
    Ctr s.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) (ciphOf m₀ (V .r29)) icb (P + j)
  done : Ctr m₀ (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) (ciphOf m₀ (V .r29)) icb P →
    bytesAt s.mem D j = xorKs (ciphOf m₀ (V .r29)) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame (V .r30) (V .r28) D n) m₀ s.mem

/-- After `crypt`. -/
structure CrOut (V : Reg → BitVec 64) (sp : Addr) (icb : Block) (P : Nat) (D : Addr) (n : Nat)
    (m₀ : Mem) (s : State) : Prop where
  env : Env V sp s
  ctr : Ctr m₀ (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) (ciphOf m₀ (V .r29)) icb P →
    Ctr s.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) (ciphOf m₀ (V .r29)) icb (P + n)
  out : Ctr m₀ (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) (ciphOf m₀ (V .r29)) icb P →
    bytesAt s.mem D n = xorKs (ciphOf m₀ (V .r29)) icb P (bytesAt m₀ D n)
  frame : Frame (crFrame (V .r30) (V .r28) D n) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
  (X : XOk (V .r29) (V .r30) (V .r31) (V .r28))
include L X

omit L X in
/-- The rest of the keystream block. -/
theorem cryptHead_ok {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (fun s' => ∃ j, j = min (16 - P % 16) n ∧ CrMid V sp icb P D n s.mem j s') := by
  obtain hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.r26 h.r25 (by omega_arith) hn') fun s₁ ⟨h5, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - P % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h5
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hk16 : P % 16 + k ≤ 16 := by omega_arith
  obtain hkn : k ≤ n := by omega_arith
  obtain e30 : s₁.gpr .r30 = V .r30 := (hg _ (by decide) (by decide)).trans he.r30
  obtain e24 : s₁.gpr .r24 = D := (hg _ (by decide) (by decide)).trans h.r24
  obtain e25 : s₁.gpr .r25 = BitVec.ofNat 64 n := (hg _ (by decide) (by decide)).trans h.r25
  obtain e26 : s₁.gpr .r26 = BitVec.ofNat 64 (P % 16) := (hg _ (by decide) (by decide)).trans h.r26
  obtain h₂ : WP isa (.block [.addi .r3 .r30 64, .add .r3 .r3 .r26, mov .r4 .r24, .add .r24 .r24 .r5,
      .sub .r25 .r25 .r5]) s₁ (fun s₂ : State =>
      s₂.gpr .r3 = V .r30 + BitVec.ofNat 64 (64 + P % 16) ∧ s₂.gpr .r4 = D ∧
      s₂.gpr .r24 = D + BitVec.ofNat 64 k ∧ s₂.gpr .r25 = BitVec.ofNat 64 (n - k) ∧
      s₂.gpr .r5 = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r24 → r ≠ .r25 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂) := by
    crun [e30, e24, e25, e26, h5, mov, BitVec.or_self]
    exact ⟨by rw [add_ofNat_assoc], ofNat_sub64 hkn hn', fun r a b c d => by simp [a, b, c, d],
      ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨h3, h4, h24, h25, h5', hg₂, hk₂⟩ => ?_)
  obtain hk₂' := hk.trans hk₂
  obtain hdk := h.data.take hkn
  obtain lp : LoopPre s₂ (V .r30 + BitVec.ofNat 64 (64 + P % 16)) D k := by
    refine ⟨h3, h4, h5', hk1, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂'.wr]; exact hdk.wr
    · exact (hdk.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [hk₂'.mem] at hm₃
  obtain hxl := length_xorBytes s.mem D (V .r30 + BitVec.ofNat 64 (64 + P % 16)) k
  obtain fw : Frame [⟨D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
  obtain hdisjst : ∀ r ∈ [(⟨D, k⟩ : Region)],
      (⟨V .r30 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨V .r30 + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hdk.ok.st.sub_right (Lay.stSub (by decide))).symm, (hdk.ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  obtain g : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r24 → r ≠ .r25 →
      s₃.gpr r = s.gpr r :=
    fun r a b c d e f i => by rw [lo.other r a b c d e, hg₂ r b c f i, hg r d e]
  obtain he₃ : Env V sp s₃ := he.keep (fun r hr => g r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) (lo.keeps.2.2.1.trans hk₂'.sp) (lo.keeps.1.trans hk₂'.rd)
    (lo.keeps.2.1.trans hk₂'.wr)
  refine ⟨k, hk'.symm, he₃, hkn, by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h24],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h25],
    h.data.of_eq (lo.keeps.1.trans hk₂'.rd) (lo.keeps.2.1.trans hk₂'.wr),
    by rw [lo.keeps.2.1, hk₂'.wr]; exact h.xw, h.dx, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc₀
    exact (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    obtain e := bytesAt_writeBytes_self s.mem D (xorBytes s.mem D (V .r30 + BitVec.ofNat 64 (64 + P % 16)) k)
      (by rw [hxl]; omega_arith)
    rw [hxl] at e
    rw [hm₃, e, xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem D k) (by rw [length_bytesAt]; exact hk16)
    rw [length_bytesAt, add_ofNat_assoc] at this
    exact this
  · exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (split_disj hkn h.data.ok.lt).symm) (by omega_arith)
  · by_cases hkk : k = n
    · left; omega_arith
    · right; omega_arith
  · exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩

omit L X in
/-- The arguments of SM4's counter mode but the data and their number. -/
theorem ctrArgs_ok {s : State} (he : Env V sp s) :
    WP isa (.block (ctrArgs 48)) s fun s' =>
      s'.gpr .r3 = V .r29 ∧ s'.gpr .r4 = V .r30 + BitVec.ofNat 64 48 ∧ s'.gpr .r7 = V .r28 ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain h29 := he.r29; have h30 := he.r30; have h28 := he.fr .r28 (by decide)
  simp only [ctrArgs]
  crun [h29, h30, h28, mov, BitVec.or_self]
  exact ⟨fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

omit L in
/-- Parts of the state are apart from SM4's working space. -/
theorem st_x {a k : Nat} (ha : a + k ≤ 80) :
    (⟨V .r30 + BitVec.ofNat 64 a, k⟩ : Region).Disjoint (xR (V .r28)) :=
  X.sx.sub_left (Lay.stSub ha)

omit L in
/-- The schedule is apart from SM4's working space. -/
theorem ctx_x : (⟨V .r29, 128⟩ : Region).Disjoint (xR (V .r28)) :=
  X.cx.sub_left (Region.sub_prefix (by decide))

/-- The arguments of SM4's counter mode on `nb` whole blocks at `D + j`. -/
theorem ctrWhole_mk {D : Addr} {j nb : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .r3 = V .r29) (h4 : s.gpr .r4 = V .r30 + BitVec.ofNat 64 48)
    (h5 : s.gpr .r5 = D + BitVec.ofNat 64 j) (h6 : s.gpr .r6 = BitVec.ofNat 64 nb)
    (h7 : s.gpr .r7 = V .r28) (hnb : nb < 2 ^ 64)
    (hdj : DataW (V .r29) (V .r30) (V .r31) s (D + BitVec.ofNat 64 j) (16 * nb))
    (hxw : Covers [xR (V .r28)] s.wr) (hdx : (⟨D + BitVec.ofNat 64 j, 16 * nb⟩ : Region).Disjoint (xR (V .r28))) :
    CtrCall s (V .r29) (V .r30 + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (V .r28) nb := by
  have hfx := X.fit
  refine ⟨h3, h4, h5, h6, h7, hnb, ?_, ?_, ctx_x X, ?_, st_x X (by decide), hdx, ?_, ?_, hdj.ok.fit, ?_,
    ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
  · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
  · have := L.cw; omega_arith
  · have := L.sw
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48) (by decide),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · exact hfx
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (he.perm.stC (by decide))) (Covers.cons (covers_left hdj.wr)
        (Covers.cons (covers_left hxw) Covers.nil)))
  · exact Covers.cons (he.perm.stC (by decide)) (Covers.cons hdj.wr (Covers.cons hxw Covers.nil))

theorem ctx_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW (V .r29) (V .r30) (V .r31) s D n) :
    ∀ r ∈ crFrame (V .r30) (V .r28) D n, (⟨V .r29, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact X.cx

theorem CrMid.ciph {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp icb P D n m₀ j s) : ciphOf s.mem (V .r29) = ciphOf m₀ (V .r29) :=
  ciph_frame h.frame (ctx_crFrame L X h.data)

/-- Whole blocks. -/
theorem cryptWhole_ok {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp icb P D n m₀ j s) :
    WP isa cryptWhole s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧ CrMid V sp icb P D n m₀ j' s' ∧
      n - j' < 16) := by
  have hn' := h.data.ok.lt
  have he := h.env
  obtain hc := h.ciph L X
  refine WP.seq (WP.mono (split_ok h.le hn' h.r24 h.r25) fun s₁ ⟨h5, h6, h24, h25, hg₁, hk₁⟩ => ?_)
  generalize hnb : (n - j) / 16 = nb at h6 h24 h25
  obtain h16 : 16 * nb ≤ n - j := by omega_arith
  obtain he₁ : Env V sp s₁ := he.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr
  obtain hd₁ := h.data.of_eq hk₁.rd hk₁.wr
  obtain hx₁ : Covers [xR (V .r28)] s₁.wr := by rw [hk₁.wr]; exact h.xw
  refine WP.ite (decide (nb = 0)) (eval_zero h6 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h24]; rfl, by rw [h25]; rfl, hd₁, hx₁, h.dx,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega_arith⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    obtain hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    obtain hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    obtain hdxj : (⟨D + BitVec.ofNat 64 j, 16 * nb⟩ : Region).Disjoint (xR (V .r28)) :=
      h.dx.sub_left (Offset.sub_base _ (by omega_arith))
    refine WP.seq (WP.mono (ctrArgs_ok he₁) fun s₂ ⟨a3, a4, a7, hg₂, hk₂⟩ => ?_)
    obtain he₂ : Env V sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
    obtain hcall := ctrWhole_mk L X he₂ a3 a4 (by rw [hg₂ _ (by decide) (by decide) (by decide), h5])
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h6]) a7 (by omega_arith)
      (hdj.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr)) (by rw [hk₂.wr]; exact hx₁) hdxj
    refine WP.mono (ctr_wp hcall) fun s₃ g => ?_
    obtain gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem] at gout gctr gframe
    obtain hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem)
      (dp := D + BitVec.ofNat 64 j) (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨j + 16 * nb, by omega_arith, ⟨he₂.of_saved g.saved g.sp g.rd g.wr, by omega_arith, ?_, ?_,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), by rw [g.wr, hk₂.wr]; exact hx₁, h.dx, ?_, ?_, ?_,
      .inr (by omega_arith), ?_⟩, by omega_arith⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h24]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h25]
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · intro hc₀
      obtain hj16 : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ (V .r29)) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        obtain e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _), List.take_left' (length_bytesAt _ _ _)] at e
      obtain hjd : bytesAt s₃.mem D j = bytesAt s.mem D j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact split_disj (D := D) (j := j) (n := n) h.le h.data.ok.lt |>.sub_right
            (Region.sub_prefix (by omega_arith))
        · exact h.dx.sub_left (Region.sub_prefix h.le)) (by omega_arith)
      exact done_append (hjd.trans (h.done hc₀)) hj16
    · have hdis : ∀ r ∈ [⟨V .r30 + BitVec.ofNat 64 48, 16⟩, ⟨D + BitVec.ofNat 64 j, 16 * nb⟩,
          xR (V .r28)],
          (⟨D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        have hst := h.data.ok.st
        obtain hs : Region.Sub ⟨D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ ⟨D, n⟩ :=
          Offset.sub_base _ (by omega_arith)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (hst.sub_left hs).sub_right (Lay.stSub (by decide))
        · rw [← add_ofNat_assoc]
          have := split_disj (D := D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega_arith)
          rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega_arith] at this
          exact this.symm
        · exact h.dx.sub_left hs
      rw [bytesAt_frame gframe hdis (by omega_arith)]
      obtain e := congrArg (List.drop (16 * nb)) h.rest
      obtain e₂ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega_arith, bytesAt_add,
          List.drop_left' (length_bytesAt _ _ _), add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base _ (by omega_arith))⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

omit L X in
/-- The keystream block zeroed and the arguments of SM4's counter mode on it. -/
theorem tailArgs_ok {s : State} (he : Env V sp s) :
    WP isa (.block tailArgs) s fun s' =>
      s'.mem = (s.mem.writeW (V .r30 + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
        (V .r30 + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .r3 = V .r29 ∧ s'.gpr .r4 = V .r30 + BitVec.ofNat 64 48 ∧
      s'.gpr .r5 = V .r30 + BitVec.ofNat 64 64 ∧ s'.gpr .r6 = BitVec.ofNat 64 1 ∧
      s'.gpr .r7 = V .r28 ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  obtain h29 := he.r29; have h30 := he.r30; have h28 := he.fr .r28 (by decide)
  obtain w₀ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  obtain w₁ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  simp only [tailArgs, ctrArgs, List.cons_append, List.nil_append]
  crun [h29, h30, h28, w₀, w₁, mov, BitVec.or_self, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e f => by simp [a, b, c, d, e, f], ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The arguments of SM4's counter mode on the keystream block. -/
theorem ctrTail_mk {s : State} (he : Env V sp s)
    (h3 : s.gpr .r3 = V .r29) (h4 : s.gpr .r4 = V .r30 + BitVec.ofNat 64 48)
    (h5 : s.gpr .r5 = V .r30 + BitVec.ofNat 64 64) (h6 : s.gpr .r6 = BitVec.ofNat 64 1)
    (h7 : s.gpr .r7 = V .r28) (hxw : Covers [xR (V .r28)] s.wr) :
    CtrCall s (V .r29) (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64)
      (V .r28) 1 := by
  have hfx := X.fit
  have hsw := L.sw
  refine ⟨h3, h4, h5, h6, h7, by decide, ?_, ?_, ctx_x X, ?_, st_x X (by decide), st_x X (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  · have := L.cw; omega_arith
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48) (by decide),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · exact hfx
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (he.perm.stC (by decide))) (Covers.cons (covers_left (he.perm.stC (by decide)))
        (Covers.cons (covers_left hxw) Covers.nil)))
  · exact Covers.cons (he.perm.stC (by decide)) (Covers.cons (he.perm.stC (by decide))
      (Covers.cons hxw Covers.nil))

/-- The last bytes' keystream block, from SM4's counter mode. -/
structure TailKs (V : Reg → BitVec 64) (sp : Addr) (icb : Block) (P : Nat) (D : Addr) (n : Nat)
    (m₀ : Mem) (j : Nat) (s₀ s : State) : Prop where
  mid : CrMid V sp icb P D n m₀ j s₀
  env : Env V sp s
  r24 : s.gpr .r24 = D + BitVec.ofNat 64 j
  r25 : s.gpr .r25 = BitVec.ofNat 64 (n - j)
  ks : blockAt s.mem (V .r30 + BitVec.ofNat 64 64) =
    ciphOf m₀ (V .r29) (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48))
  cb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) =
    Spec.Gcm.inc32 (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48))
  frame : Frame [⟨V .r30 + BitVec.ofNat 64 48, 32⟩, xR (V .r28)] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The new keystream block. -/
theorem tailKs_ok {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp icb P D n m₀ j s) :
    WP isa (.seq (.block tailArgs) Impl.Sm4.PPC64LE.ctr32) s (TailKs V sp icb P D n m₀ j s) := by
  have he := h.env
  obtain hc := h.ciph L X
  refine WP.seq (WP.mono (tailArgs_ok he) fun s₂ ⟨hm₂, a3, a4, a5, a6, a7, hg₂, hk₂⟩ => ?_)
  obtain he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd
    hk₂.wr
  obtain fz : Frame [⟨V .r30 + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store2 _ _ _
  obtain hKS0 : blockAt s₂.mem (V .r30 + BitVec.ofNat 64 64) = 0 := by
    rw [hm₂, blockAt, zeroT_bytes]; decide
  obtain hCB : blockAt s₂.mem (V .r30 + BitVec.ofNat 64 48) = blockAt s.mem (V .r30 + BitVec.ofNat 64 48) :=
    blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  obtain hc₂ : ciphOf s₂.mem (V .r29) = ciphOf m₀ (V .r29) := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))), hc]
  refine WP.mono (ctr_wp (ctrTail_mk L X he₂ a3 a4 a5 a6 a7 (by rw [hk₂.wr]; exact h.xw))) fun s₃ g => ?_
  obtain gout := g.out; have gctr := g.ctr; have gframe := g.frame
  rw [blocksAt_one, blocksAt_one, hKS0, Proof.Cmac.ctr32_one,
    List.cons.injEq] at gout
  refine ⟨h, he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, ?_, ?_, ?_, by rw [g.rd, hk₂.rd], by rw [g.wr, hk₂.wr]⟩
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.r24]
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.r25]
  · rw [gout.1, ← hc₂, hCB]
  · rw [gctr, hCB]; rfl
  · refine (fz.sub fun r hr => ?_).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

omit L X in
/-- The last bytes XORed with the new keystream block. -/
theorem tailXor_ok {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s₀ s : State}
    (h : TailKs V sp icb P D n m₀ j s₀ s) (hj : n - j < 16) (h0 : n - j ≠ 0) :
    WP isa (.seq (.block [.addi .r3 .r30 64, mov .r4 .r24, mov .r5 .r25]) xorLoop) s
      (CrOut V sp icb P D n m₀) := by
  have hm := h.mid
  have hn' := hm.data.ok.lt
  obtain hw : (P + j) % 16 = 0 := hm.whole.resolve_left h0
  obtain hdj := hm.data.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
  have he₃ := h.env
  have h30 := he₃.r30
  obtain h₄ : WP isa (.block [.addi .r3 .r30 64, mov .r4 .r24, mov .r5 .r25]) s fun s₄ =>
      s₄.gpr .r3 = V .r30 + BitVec.ofNat 64 64 ∧ s₄.gpr .r4 = D + BitVec.ofNat 64 j ∧
      s₄.gpr .r5 = BitVec.ofNat 64 (n - j) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₄.gpr r = s.gpr r) ∧ Keeps s s₄ := by
    crun [h30, h.r24, h.r25, mov, BitVec.or_self]
    exact ⟨fun r a b d => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₄ fun s₄ ⟨h3, h4, h5, hg₄, hk₄⟩ => ?_)
  obtain lp : LoopPre s₄ (V .r30 + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j) := by
    refine ⟨h3, h4, h5, by omega_arith, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₄.rd, hk₄.wr]; exact covers_left (he₃.perm.stC (by omega_arith))
    · rw [hk₄.wr, h.wr]; exact hdj.wr
    · exact (hdj.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, lo⟩ => ?_
  rw [hk₄.mem] at hm₅
  obtain hxl := length_xorBytes s.mem (D + BitVec.ofNat 64 j) (V .r30 + BitVec.ofNat 64 64) (n - j)
  obtain fw : Frame [⟨D + BitVec.ofNat 64 j, n - j⟩] s.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ hxl
  have dst := hdj.ok.st
  obtain dx : (⟨D + BitVec.ofNat 64 j, n - j⟩ : Region).Disjoint (xR (V .r28)) :=
    hm.dx.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hd₃ : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
    rw [← hm.rest, bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dst.sub_right (Lay.stSub (by decide))
    · exact dx
  obtain ht := fun hc₀ => Proof.Gcm.ctr_tail (hm.ctr hc₀) hw (m₁ := s.mem) h.ks (by rw [h.cb])
    (d := bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) (by rw [length_bytesAt]; omega_arith)
    (by rw [length_bytesAt]; omega_arith)
  rw [length_bytesAt] at ht
  obtain dS : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
      (⟨V .r30 + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
    intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
    exact (dst.sub_right (Lay.stSub hk)).symm
  obtain g : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₅.gpr r = s.gpr r :=
    fun r a b c d e => by rw [lo.other r a b c d e, hg₄ r b c d]
  refine ⟨he₃.keep (fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide))
      (lo.keeps.2.2.1.trans hk₄.sp) (lo.keeps.1.trans hk₄.rd) (lo.keeps.2.1.trans hk₄.wr), ?_, ?_, ?_⟩
  · intro hc₀
    rw [show P + n = P + j + (n - j) by omega_arith]
    exact (ht hc₀).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
      (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
  · intro hc₀
    obtain hdone : bytesAt s₅.mem D j = bytesAt s₀.mem D j := by
      obtain hdt := (hm.data.take hm.le).ok
      rw [bytesAt_frame fw (fun r hr => ?_) (by omega_arith), bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hdt.st.sub_right (Lay.stSub (by decide))
        · exact hm.dx.sub_left (Region.sub_prefix hm.le)
      · simp only [List.mem_singleton] at hr; subst hr; exact split_disj hm.le hm.data.ok.lt
    obtain hpiece : bytesAt s₅.mem (D + BitVec.ofNat 64 j) (n - j) =
        xorKs (ciphOf m₀ (V .r29)) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) := by
      obtain e := bytesAt_writeBytes_self s.mem (D + BitVec.ofNat 64 j)
        (xorBytes s.mem (D + BitVec.ofNat 64 j) (V .r30 + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [hm₅, e, xorBytes, hd₃, (ht hc₀).1]
    rw [show n = j + (n - j) by omega_arith]
    exact done_append (hdone.trans (hm.done hc₀)) hpiece
  · refine hm.frame.trans (Frame.trans (h.frame.sub fun r hr => ?_) (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp icb P D n m₀ j s) (hj : n - j < 16) :
    WP isa cryptTail s (CrOut V sp icb P D n m₀) := by
  have hn' := h.data.ok.lt
  refine WP.ite (decide (n - j = 0)) (eval_zero h.r25 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega_arith
    subst h0
    exact WP.block_nil ⟨h.env, fun hc₀ => h.ctr hc₀, fun hc₀ => h.done hc₀, h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (tailKs_ok L X h) fun _ ht => tailXor_ok ht hj h0)

omit L X in
/-- The rest of the keystream block first, if there is one. -/
theorem cryptFill_ok {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp icb P D n s) (h0 : n ≠ 0) :
    WP isa cryptFill s (fun s' => ∃ j, j = (if P % 16 = 0 then 0 else min (16 - P % 16) n) ∧
      CrMid V sp icb P D n s.mem j s') := by
  refine WP.ite (decide (P % 16 = 0)) (eval_zero h.r26 (by have := Nat.mod_lt P (show 16 > 0 by decide); omega_arith))
    (fun ht => ?_) (fun hf => ?_)
  · have ho : P % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h.env, by omega_arith, by rw [h.r24, BitVec.add_zero], by rw [h.r25, Nat.sub_zero],
      h.data, h.xw, h.dx, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl,
      by rw [BitVec.add_zero, Nat.sub_zero], .inr (by omega_arith), Frame.refl _ _⟩
  · have hP : P % 16 ≠ 0 := by simpa using hf
    exact WP.mono (cryptHead_ok h h0 hP) fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [hP, ite_false]; exact hj, hm⟩

/-- `crypt`. -/
theorem crypt_ok {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp icb P D n s) :
    WP isa crypt s (CrOut V sp icb P D n s.mem) := by
  have hn' := h.data.ok.lt
  refine WP.ite (decide (n = 0)) (eval_zero h.r25 hn') (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h.env, fun hc₀ => hc₀, fun _ => by simp [bytesAt]; rfl, Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (cryptFill_ok h h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (cryptWhole_ok L X hj) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact cryptTail_ok L X hj' hlt

end

end VG.Proof.Sm4Gcm.PPC64LE
