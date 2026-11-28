module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.Lemmas

-- separate module: `WotsMain` builds on it; keeping the chains' blocks here keeps each module's proofs small.

/-!
# SLH-DSA on AArch64: `wotsLeaves4`, the steps of the chains

As on x86-64 (`Proof/SlhDsa/X86_64/WotsMain.lean`): what the lanes of `A`
hold (`LaneA`): an address of the type `ty`, key pair `κ`, chain `c`, hash
`h`, and the message `M`, so that `thash4` computes `F`, or `PRF`
(`laneA_msg`); the blocks of a chain: the private key values (`prfLanes`),
the type `WOTS_HASH` (`hashType`), the hash addresses (`hashAdrs`) and the
masked capture of the signature (`capture`); and the 15 steps of a chain.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Wots4

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64
open VG.Proof.SlhDsa (fld)

variable {p : Params} {σ : State} {S sig : Addr} {kp idx : Nat} {pkSeed a16 skSeed : List Byte}

/-- The temporaries of the blocks. -/
abbrev TMP : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

theorem nt {g : Reg} (hg : g ∉ TMP) (r : Reg) (hr : r ∈ TMP := by decide) : g ≠ r := fun e => hg (e ▸ hr)

theorem br_tmp {g : Reg} (hg : g ∈ BR) : g ∉ TMP := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Bytes, split -/

theorem bytesAt_split (m : Mem) (S : Addr) (a x y : Nat) :
    bytesAt m (at' S a) (x + y) = bytesAt m (at' S a) x ++ bytesAt m (at' S (a + x)) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, ofNat_add', Nat.add_assoc]

/-- A lane's `PK.seed`, address and message. -/
theorem lane_msg (m : Mem) (S : Addr) (b n L : Nat) :
    bytesAt m (at' S b) (n + 32 + L) = bytesAt m (at' S b) n ++ (bytesAt m (at' S (b + n)) 16 ++
      (bytesAt m (at' S (b + n + 16)) 4 ++ (bytesAt m (at' S (b + n + 20)) 4 ++ (bytesAt m (at' S (b + n + 24)) 4 ++
        (bytesAt m (at' S (b + n + 28)) 4 ++ bytesAt m (at' S (b + n + 32)) L))))) := by
  rw [show n + 32 + L = n + (16 + (4 + (4 + (4 + (4 + L))))) by omega_using [], bytesAt_split, bytesAt_split,
    bytesAt_split, bytesAt_split, bytesAt_split, bytesAt_split]

/-! ## The lanes of `A` -/

/-- `l` bytes at `off` (from 16) after lane `k`'s `PK.seed` in `A`. -/
abbrev la (p : Params) (m : Mem) (S : Addr) (k off l : Nat) : List Byte :=
  bytesAt m (at' S (Layout.laneA k + p.n + off)) l

/-- Lane `k` of `A`: the type `ty`, key pair `κ`, chain `c`, hash `h`, message `M`. -/
structure LaneA (p : Params) (m : Mem) (S : Addr) (k ty κ c h : Nat) (M : List Byte) : Prop where
  f16 : la p m S k 16 4 = toByte ty 4
  f20 : la p m S k 20 4 = toByte κ 4
  f24 : la p m S k 24 4 = toByte c 4
  f28 : la p m S k 28 4 = toByte h 4
  msg : la p m S k 32 p.n = M

/-- A range of lane `k₂` that a change of a range of lane `k₁` leaves. -/
theorem la_keep (hz : Sz p) {m m' : Mem} {S : Addr} {k₁ o₁ l₁ k₂ o₂ l₂ : Nat}
    (hf : Frame [⟨at' S (Layout.laneA k₁ + p.n + o₁), l₁⟩] m m') (hk₁ : k₁ < 4) (hk₂ : k₂ < 4)
    (h₁ : 16 ≤ o₁) (h₁' : o₁ + l₁ ≤ p.n + 32) (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ p.n + 32)
    (h : k₁ ≠ k₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) : la p m' S k₂ o₂ l₂ = la p m S k₂ o₂ l₂ := by
  have hn := hz.n32
  exact keepScr hf (by rw [laneA_eq, laneA_eq]; omega_using [h, hk₁, hk₂, h₁, h₁', h₂, h₂', hn])
    (by rw [laneA_eq]; omega_using [hk₁, h₁', hn]) (by rw [laneA_eq]; omega_using [hk₂, h₂', hn])

/-- The fields and message of lane `k`, after its `PK.seed` and `a16`. -/
abbrev laneR (p : Params) (S : Addr) (k : Nat) : Region := ⟨at' S (Layout.laneA k + p.n + 16), p.n + 16⟩

theorem LaneA.keep (hz : Sz p) {m m' : Mem} {S : Addr} {k k' ty κ c h : Nat} {M : List Byte}
    (hl : LaneA p m S k' ty κ c h M) (hf : Frame [laneR p S k] m m') (hk : k < 4) (hk' : k' < 4) (hne : k ≠ k') :
    LaneA p m' S k' ty κ c h M := by
  have hn := hz.n32
  have e : ∀ o l, 16 ≤ o → o + l ≤ p.n + 32 → la p m' S k' o l = la p m S k' o l := fun o l h₁ h₂ =>
    la_keep hz (o₁ := 16) hf hk hk' (by omega_using []) (by omega_using []) h₁ h₂ (Or.inl hne)
  exact ⟨by rw [e 16 4 (by omega_using []) (by omega_using [hn]), hl.f16],
    by rw [e 20 4 (by omega_using []) (by omega_using [hn]), hl.f20],
    by rw [e 24 4 (by omega_using []) (by omega_using [hn]), hl.f24],
    by rw [e 28 4 (by omega_using []) (by omega_using [hn]), hl.f28],
    by rw [e 32 p.n (by omega_using []) (by omega_using []), hl.msg]⟩

theorem laneR_tail (hz : Sz p) {k : Nat} (hk : k < 4) (S sig : Addr) (kp : Nat) :
    ∃ R ∈ wch p S sig kp, Region.Sub (laneR p S k) R := by
  have hn := hz.n32
  refine ⟨_, tailA_mem k hk S sig kp, ?_⟩
  have e := sub_tailA (p := p) (S := S) (k := k) (a := p.n + 16) (l := p.n + 16) (by omega_using [])
    (by rw [strideA_eq]; omega_using [hn])
  rwa [← Nat.add_assoc] at e

/-- A range of lane `k` is in `laneR`. -/
theorem la_sub {S : Addr} {k o l : Nat} (h₁ : 16 ≤ o) (h₂ : o + l ≤ p.n + 32) :
    Region.Sub ⟨at' S (Layout.laneA k + p.n + o), l⟩ (laneR p S k) := by
  have e : at' S (Layout.laneA k + p.n + o) = at' S (Layout.laneA k + p.n + 16) + BitVec.ofNat 64 (o - 16) := by
    rw [ofNat_add', show Layout.laneA k + p.n + 16 + (o - 16) = Layout.laneA k + p.n + o by omega_using [h₁]]
  rw [e]; exact Offset.sub_base _ (by omega_using [h₁, h₂])

theorem laneR_save (hz : Sz p) {k : Nat} (hk : k < 4) (S : Addr) : Region.Disjoint (saveR S) (laneR p S k) := by
  have hn := hz.n32
  exact Entry.dscr (Or.inl (by rw [laneA_eq]; omega_using [])) (by decide) (by rw [laneA_eq]; omega_using [hk, hn])

/-- The message of lane `k` of `A` to `thash4`. -/
theorem laneA_msg {m : Mem} (henv : Env p m S pkSeed a16) {k ty κ c h : Nat} {M : List Byte} (hk : k < 4)
    (hl : LaneA p m S k ty κ c h M) :
    bytesAt m (at' S (Layout.laneA k)) (2 * p.n + 32) = pkSeed ++ fld a16 ty κ c h ++ M := by
  rw [show 2 * p.n + 32 = p.n + 32 + p.n by omega_using [], lane_msg, henv.seedA k hk, henv.adrsA k hk]
  obtain ⟨f16, f20, f24, f28, fm⟩ := hl
  simp only [la] at f16 f20 f24 f28 fm
  rw [f16, f20, f24, f28, fm]
  simp only [fld, List.append_assoc]

/-! ## The chains, in the specification -/

theorem a16_length {m : Mem} (henv : Env p m S pkSeed a16) : a16.length = 16 := by
  rw [← henv.adrsA 0 (by decide), bytesAt_length']

/-- The private key value. -/
theorem chainAt_zero (hz : Sz p) (h16 : a16.length = 16) {κ : Nat} (hκ : κ < 2 ^ 32) (i : Nat) :
    wotsChainAt p skSeed pkSeed a16 κ i 0 = shake256 (pkSeed ++ fld a16 WOTS_PRF κ i 0 ++ skSeed) p.n := by
  simp only [wotsChainAt, chain, List.range_zero, List.foldl_nil, prf, hz.shake, shakeAdrs]
  rw [VG.Proof.SlhDsa.wotsAdrs_fld h16, VG.Proof.SlhDsa.wotsSkAdrs_fld h16 _ _ _ _ hκ,
    VG.Proof.SlhDsa.setChainAddress_fld h16]

/-- A step of the chain: `F` with the hash address `j`. -/
theorem chainAt_succ (hz : Sz p) (h16 : a16.length = 16) (κ i j : Nat) :
    wotsChainAt p skSeed pkSeed a16 κ i (j + 1) =
      shake256 (pkSeed ++ fld a16 WOTS_HASH κ i j ++ wotsChainAt p skSeed pkSeed a16 κ i j) p.n := by
  simp only [wotsChainAt, chain, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
  rw [VG.Proof.SlhDsa.wotsAdrs_fld h16, VG.Proof.SlhDsa.setChainAddress_fld h16,
    VG.Proof.SlhDsa.setHashAddress_fld h16]
  simp only [F, hz.shake, shakeAdrs]

/-! ## Writes in a lane of `A`, with `Base` -/

theorem tailA_of (hz : Sz p) {k o : Nat} (hk : k < 4) (h₁ : 16 ≤ o) (h₂ : o ≤ 28) : InTail p (Layout.laneA k + p.n + o) :=
  ⟨k, hk, Or.inl ⟨by omega_using [h₁], by rw [strideA_eq]; have := hz.n32; omega_using [h₂, this]⟩⟩

theorem laneA_al (hz : Sz p) {k o : Nat} (ho : o % 4 = 0) : (Layout.laneA k + p.n + o) % 4 = 0 := by
  have := hz.n8; rw [laneA_eq]; omega_using [this, ho]

/-- A copy into lane `k`'s message, with `Base`. -/
theorem copyA_base (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {t : State} (hb : Base hE t)
    {k src : Nat} (hk : k < 4) (hsrc : src + p.n ≤ 12480) (hs8 : src % 8 = 0)
    (hd : Region.Disjoint ⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ ⟨at' S src, p.n⟩) {Q : State → Prop}
    (kk : ∀ t', Base hE t' → (∀ g, g ≠ .x14 → t'.gpr g = t.gpr g) →
      la p t'.mem S k 32 p.n = bytesAt t.mem (at' S src) p.n →
      Frame [⟨at' S (Layout.laneA k + p.n + 32), p.n⟩] t.mem t'.mem → Q t') :
    WP isa (.block (copyWords .x19 (Layout.laneA k + (L p).msgOff) .x19 src (p.n / 8))) t Q := by
  have hn := hz.n32
  have h8 : 8 * (p.n / 8) = p.n := by have := hz.n8; omega_using [this]
  have hdst : at' S (Layout.laneA k + (L p).msgOff) = at' S (Layout.laneA k + p.n + 32) := by
    simp only [Layout.msgOff, Nat.add_assoc]
  refine WP.mono (copyWords_ok (s := t) (by decide) (by decide) hs8
    (by simp only [Layout.msgOff]; rw [laneA_eq]; have := hz.n8; omega_using [this]) ?_ ?_ ?_ ?_ ?_) fun t' c => ?_
  · rw [hb.x19, h8]; exact hE.inScr' hb.wr (by omega_using [hsrc])
  · rw [hb.x19, h8]; exact hE.inScr hb.wr (by rw [laneA_eq]; simp only [Layout.msgOff]; omega_using [h8, hn, hk])
  · rw [hb.x19, h8]; show Region.Disjoint ⟨at' S _, _⟩ ⟨at' S _, _⟩; rw [hdst]; exact hd
  · omega_using [h8, hsrc]
  · rw [laneA_eq]; simp only [Layout.msgOff]; omega_using [h8, hn, hk]
  rw [hb.x19, h8] at c
  change CopyPost t t' (at' S _) (at' S _) _ at c
  rw [hdst] at c
  obtain ⟨R, hR, hs⟩ := laneR_tail hz hk S sig kp
  refine kk t' (hb.ofFrame c.rd c.wr c.sp (fun g hg => c.gpr g (ne_of_mem hg (by decide))) c.frame
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨R, hR, fun x hx => hs x (la_sub (by omega_using []) (by omega_using []) x hx)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (laneR_save hz hk S).sub_right (la_sub (by omega_using []) (by omega_using []))))
    c.gpr (bytesAt_ext fun q hq => c.bytes q hq) c.frame

/-- Lane `k` of `A` for `PRF`. -/
theorem prfLane_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k i : Nat} (hk : k < 4)
    (hi : i < 2 ^ 32) {t : State} (hb : Base hE t) (hr : t.gpr .x21 = BitVec.ofNat 64 i) :
    WP isa (.block (Wots.prfLane (L p) k)) t (fun t' => Base hE t' ∧ (∀ g ∉ TMP, t'.gpr g = t.gpr g) ∧
      la p t'.mem S k 16 4 = toByte WOTS_PRF 4 ∧ la p t'.mem S k 24 4 = toByte i 4 ∧
      la p t'.mem S k 28 4 = toByte 0 4 ∧ la p t'.mem S k 32 p.n = skSeed ∧
      la p t'.mem S k 20 4 = la p t.mem S k 20 4 ∧ Frame [laneR p S k] t.mem t'.mem) := by
  have hn := hz.n32
  simp only [Wots.prfLane, List.append_assoc, Layout.adrsOff]
  refine setField_base hE hb (tailA_of hz hk (by decide) (by decide)) (laneA_al hz (by decide)) (by decide)
    fun t₁ b₁ g₁ y₁ f₁ => ?_
  have hv : (t₁.gpr .x21).toNat = i := by rw [g₁ _ (by decide), hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi])]
  refine setFieldR_base hE b₁ (tailA_of hz hk (by decide) (by decide)) (laneA_al hz (by decide)) (by rw [hv]; exact hi)
    fun t₂ b₂ g₂ y₂ f₂ => ?_
  refine setField_base hE b₂ (tailA_of hz hk (by decide) (by decide)) (laneA_al hz (by decide)) (by decide)
    fun t₃ b₃ g₃ y₃ f₃ => ?_
  refine copyA_base hE hz b₃ hk (src := Layout.oSkSeed) (by rw [oSkSeed_eq]; omega_using [hn]) (by decide)
    (Entry.dscr (Or.inr (by rw [laneA_eq, oSkSeed_eq]; omega_using [hn])) (by rw [laneA_eq]; omega_using [hk, hn])
      (by rw [oSkSeed_eq]; omega_using [hn])) fun t₄ b₄ g₄ y₄ f₄ => ?_
  rw [hv] at y₂
  have K := fun {m m' : Mem} {o₁ l₁ o₂ l₂ : Nat} (hf : Frame [⟨at' S (Layout.laneA k + p.n + o₁), l₁⟩] m m')
    (h₁ : 16 ≤ o₁) (h₁' : o₁ + l₁ ≤ p.n + 32) (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ p.n + 32)
    (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) => la_keep hz hf hk hk h₁ h₁' h₂ h₂' (Or.inr h)
  refine ⟨b₄, fun g hg => by rw [g₄ g (nt hg .x14), g₃ g (nt hg .x9), g₂ g (nt hg .x9), g₁ g (nt hg .x9)], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K f₄ (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₃ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₂ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using [])]
    exact y₁
  · rw [K f₄ (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₃ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using [])]
    exact y₂
  · rw [K f₄ (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [hn]) (by omega_using [])]
    exact y₃
  · rw [y₄]; exact (b₃.sk hz)
  · rw [K f₄ (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₃ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₂ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₁ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using [])]
  · have s : ∀ {o l : Nat}, 16 ≤ o → o + l ≤ p.n + 32 → ∀ r ∈ [(⟨at' S (Layout.laneA k + p.n + o), l⟩ : Region)],
        ∃ R ∈ [laneR p S k], Region.Sub r R := fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, la_sub h₁ h₂⟩
    exact (((f₁.sub (s (by omega_using []) (by omega_using [hn]))).trans (f₂.sub (s (by omega_using [])
      (by omega_using [hn])))).trans (f₃.sub (s (by omega_using []) (by omega_using [hn])))).trans
      (f₄.sub (s (by omega_using []) (by omega_using [])))

/-! ## The capture -/

/-- Chain `i` of the signature. -/
abbrev sigC (p : Params) (m : Mem) (sig : Addr) (i : Nat) : List Byte := bytesAt m (sig + BitVec.ofNat 64 (i * p.n)) p.n

theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b :=
  ⟨fun h => by
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this,
   fun h => by rw [h]⟩

theorem toNat_lt_of {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 64 a).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h])]; exact h

/-- The mask of `captureLane`: all ones exactly if `A = B` and `C = E`. -/
theorem mask_eq {A B C E : BitVec 64} (hA : A.toNat < 2 ^ 32) (hB : B.toNat < 2 ^ 32) (hC : C.toNat < 2 ^ 32)
    (hE : E.toNat < 2 ^ 32) :
    (0 : BitVec 64) - ((((A ^^^ B) ||| (C ^^^ E)) - 1) >>> 63) = if A = B ∧ C = E then BitVec.allOnes 64 else 0 := by
  have hx : ((A ^^^ B) ||| (C ^^^ E)).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_or, BitVec.toNat_xor, BitVec.toNat_xor]
    exact Nat.or_lt_two_pow (Nat.xor_lt_two_pow hA hB) (Nat.xor_lt_two_pow hC hE)
  rw [mask_zero (by omega_using [hx])]
  have e : ((A ^^^ B) ||| (C ^^^ E)) = 0 ↔ (A = B ∧ C = E) := by
    show A ^^^ B ||| C ^^^ E = 0#64 ↔ _
    rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff]
  by_cases h : A = B ∧ C = E
  · rw [ite_eq_left (e.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (e.mp h')), ite_eq_right h]

theorem captureLane_eq (L : Layout) (k : Nat) : Wots.captureLane L k =
    ([.addImm .x .x12 .x20 k, .logic .eor .x .x12 .x12 .x23, .logic .orr .x .x12 .x12 .x10] : List Instr) ++
      maskZero .x12 .x13 ++
      (List.range (L.n / 8)).flatMap (selWord .x11 .x19 (Layout.laneA k + L.msgOff)) := rfl

/-- The masked copy of lane `k`'s value into chain `i` of the signature (at `x11`). -/
theorem capLane_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k i j : Nat} {D : BitVec 64}
    (hk : k < 4) (hi : i < p.len) (hj : j < 2 ^ 32) (hD : D.toNat < 2 ^ 32) {t : State} (hb : Base hE t)
    (hdx : t.gpr .x10 = BitVec.ofNat 64 j ^^^ D) (hsi : t.gpr .x11 = sig + BitVec.ofNat 64 (i * p.n)) :
    WP isa (.block (Wots.captureLane (L p) k)) t (fun t' => Base hE t' ∧
      (∀ g, g ≠ .x12 → g ≠ .x13 → g ≠ .x14 → t'.gpr g = t.gpr g) ∧
      sigC p t'.mem sig i = (if kp + k = idx ∧ j = D.toNat then la p t.mem S k 32 p.n else sigC p t.mem sig i) ∧
      Frame [⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩] t.mem t'.mem) := by
  have hn := hz.n32
  have hkp := hE.kp_lt hz
  have h8 : 8 * (p.n / 8) = p.n := by have := hz.n8; omega_using [this]
  have hlen : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  rw [captureLane_eq]
  simp only [maskZero, List.cons_append, List.nil_append]
  refine wp_addImm (by omega_using [hk]) fun t₁ u₁ => wp_eor fun t₂ u₂ => wp_orr fun t₃ u₃ =>
    wp_subImm (by decide) fun t₄ u₄ => wp_lsr (by decide) fun t₅ u₅ => wp_movz fun t₆ u₆ => wp_sub fun t₇ u₇ => ?_
  have hg : ∀ g, g ≠ .x12 → g ≠ .x13 → t₇.gpr g = t.gpr g := fun g h₁ h₂ => by
    rw [u₇.other _ h₁, u₆.other _ h₂, u₅.other _ h₁, u₄.other _ h₁, u₃.other _ h₁, u₂.other _ h₁, u₁.other _ h₁]
  have hm₇ : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hb₇ : Base hE t₇ := hb.regs hm₇ (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
    fun g h' => hg g (ne_of_mem h' (by decide)) (ne_of_mem h' (by decide))
  let P := kp + k = idx ∧ j = D.toNat
  have hmask : t₇.gpr .x12 = if decide P then BitVec.allOnes 64 else 0 := by
    have a1 : t₁.gpr .x12 = BitVec.ofNat 64 (kp + k) := by rw [u₁.gpr, hb.x20, ← BitVec.ofNat_add]
    have a2 : t₂.gpr .x12 = BitVec.ofNat 64 (kp + k) ^^^ BitVec.ofNat 64 idx := by
      rw [u₂.gpr, a1, u₁.other _ (by decide), hb.x23]
    have a3 : t₃.gpr .x12 = (BitVec.ofNat 64 (kp + k) ^^^ BitVec.ofNat 64 idx) ||| (BitVec.ofNat 64 j ^^^ D) := by
      rw [u₃.gpr, a2, u₂.other _ (by decide), u₁.other _ (by decide), hdx]
    have a5 : t₅.gpr .x12 = ((((BitVec.ofNat 64 (kp + k) ^^^ BitVec.ofNat 64 idx) |||
        (BitVec.ofNat 64 j ^^^ D)) - 1) >>> 63) := by
      rw [u₅.gpr, u₄.gpr, a3]; rfl
    have d6 : t₆.gpr .x13 = 0 := by rw [u₆.gpr]; rfl
    rw [u₇.gpr, d6, u₆.other _ (by decide), a5,
      mask_eq (toNat_lt_of (by omega_using [hkp, hk])) (toNat_lt_of hE.idx32) (toNat_lt_of hj) hD]
    have e : (BitVec.ofNat 64 (kp + k) = BitVec.ofNat 64 idx ∧ BitVec.ofNat 64 j = D) ↔ P := by
      rw [ofNat_eq_iff (by omega_using [hkp, hk]) (by have := hE.idx32; omega_using [this])]
      refine and_congr Iff.rfl ⟨fun h => by rw [← h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj])],
        fun h => by rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
    by_cases c : P
    · rw [ite_eq_left (e.mpr c), decide_eq_true c]; rfl
    · rw [ite_eq_right (fun h => c (e.mp h)), decide_eq_false c]; rfl
  have hsi₇ : t₇.gpr .x11 = sig + BitVec.ofNat 64 (i * p.n) := by rw [hg _ (by decide) (by decide), hsi]
  have hfit : (sig + BitVec.ofNat 64 (i * p.n)).toNat + p.n ≤ 2 ^ 64 := by
    have hf := hE.reg.out_fit; simp only at hf
    have h16 := hz.n16
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hf, hlen, h16]),
      Nat.mod_eq_of_lt (by omega_using [hf, hlen, h16])]
    omega_using [hf, hlen]
  refine WP.mono (selWords_ok (s := t₇) (dst := .x11) (src := .x19) (d₁ := Layout.laneA k + (L p).msgOff)
    (w := p.n / 8) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ hmask
    (by simp only [Layout.msgOff]; rw [laneA_eq]; have := hz.n8; omega_using [this])
    (by simp only [Layout.msgOff]; rw [laneA_eq]; omega_using [h8, hn, hk]) (by omega_using [h8, hn]) ?_ ?_ ?_) fun t' c => ?_
  · rw [hb₇.x19, h8]
    exact hE.inScr' hb₇.wr (by rw [laneA_eq]; simp only [Layout.msgOff]; omega_using [h8, hn, hk])
  · rw [hsi₇, h8]
    have := hE.inSig (o := i * p.n) (n := p.n) hb₇.wr (by omega_using [hlen]) (by have := hz.n16; omega_using [this])
    exact this
  · rw [hsi₇, hb₇.x19, h8]
    have := hE.dsig (o := i * p.n) (l := p.n) (a := Layout.laneA k + p.n + 32) (m := p.n) (by omega_using [hlen])
      (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])
    simp only [Layout.msgOff, ← Nat.add_assoc]; exact this
  rw [hsi₇, hb₇.x19, h8] at c
  have hsub : ∀ r ∈ [(⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ : Region)], ∃ R ∈ wch p S sig kp,
      Region.Sub r R := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨sig, p.len * p.n⟩, sig_mem S sig kp, Offset.sub_base _ (by omega_using [hlen])⟩
  refine ⟨hb₇.ofFrame c.rd c.wr c.sp (fun g hg' => by
      rw [c.gpr g (ne_of_mem hg' (by decide)) (ne_of_mem hg' (by decide))])
      c.frame hsub (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hE.dsig (o := i * p.n) (l := p.n) (a := 1024) (m := 56) (by omega_using [hlen])
          (by rw [oSigTmp_eq]; decide)).symm),
    fun g h₁ h₂ h₃ => by rw [c.gpr g h₂ h₃, hg g h₁ h₂], ?_, by rw [← hm₇]; exact c.frame⟩
  have hsrc : at' S (Layout.laneA k + p.n + 32) = S + BitVec.ofNat 64 (Layout.laneA k + (L p).msgOff) := by
    simp only [Layout.msgOff, Nat.add_assoc]
  by_cases hc : P
  · rw [ite_eq_left hc]
    exact bytesAt_ext fun q hq => by rw [c.bytes q hq, decide_eq_true hc, ite_eq_left rfl, hm₇, hsrc]
  · rw [ite_eq_right hc]
    exact bytesAt_ext fun q hq => by rw [c.bytes q hq, decide_eq_false hc, hm₇]; rfl

/-- The value chain `i` of lane `k` holds after `j` steps. -/
abbrev cv (p : Params) (skSeed pkSeed a16 : List Byte) (kp k i j : Nat) : List Byte :=
  wotsChainAt p skSeed pkSeed a16 (kp + k) i j

/-- Whether the signature's key pair is one of the four. -/
abbrev InR (kp idx : Nat) : Prop := kp ≤ idx ∧ idx < kp + 4

theorem captureLanes_tail (L : Layout) :
    Wots.capture L = ([.add .x .x9 .x19 .x21, .ldrb .x9 .x9 Layout.oDigits, .logic .eor .x .x10 .x22 .x9,
      Thash4.mov .x11 .x21] : List Instr) ++ mulN L.n .x11 .x12 ++ ([.add .x .x11 .x11 .x24] : List Instr) ++
      (List.range 4).flatMap (Wots.captureLane L) := rfl

/-- The capture at step `j` of chain `i`: the signature's chain `i` gets
lane `k`'s value if `kp + k = idx` and `j` is digit `i`. -/
theorem capture_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {i j : Nat} (hi : i < p.len)
    (hj : j < 16) {t : State} (hb : Base hE t) (hr21 : t.gpr .x21 = BitVec.ofNat 64 i)
    (hr22 : t.gpr .x22 = BitVec.ofNat 64 j) (hl : ∀ k < 4, la p t.mem S k 32 p.n = cv p skSeed pkSeed a16 kp k i j) :
    WP isa (.block (Wots.capture (L p))) t (fun t' => Base hE t' ∧
      (∀ g ∉ TMP, t'.gpr g = t.gpr g) ∧
      sigC p t'.mem sig i = (if InR kp idx ∧ j = digitAt σ.mem S i then
        wotsChainAt p skSeed pkSeed a16 idx i j else sigC p t.mem sig i) ∧
      Frame [⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩] t.mem t'.mem) := by
  have hn := hz.n32
  have hlen : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  have hdig := hE.dig i hi
  have hlt : Layout.oDigits + i + 1 ≤ 65536 := by rw [oDigits_eq]; have := hz.len; omega_using [hi, this, hn]
  rw [captureLanes_tail]
  simp only [Thash4.mov, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_add fun t₁ u₁ => ?_
  have h9 : t₁.gpr .x9 + BitVec.ofNat 64 Layout.oDigits = at' S (Layout.oDigits + i) := by
    rw [u₁.gpr, hb.x19, hr21, ofNat_add', Nat.add_comm]
  refine wp_ldrb (by rw [oDigits_eq]; decide) h9 (by rw [u₁.rd, u₁.wr]; exact hE.inScr' hb.wr hlt)
    fun t₂ u₂ => wp_eor fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ => ?_
  let D : BitVec 64 := (σ.mem (at' S (Layout.oDigits + i))).setWidth 64
  have hD : D.toNat = digitAt σ.mem S i := by
    simp only [D, digitAt, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))
  have hg₄ : ∀ g, g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → t₄.gpr g = t.gpr g := fun g h₁ h₂ h₃ => by
    rw [u₄.other _ h₃, u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₁]
  have hdx : t₄.gpr .x10 = BitVec.ofNat 64 j ^^^ D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hr22, u₁.mem,
      hb.digit hz hi]
  refine mulN_ok hz.nv (r := .x11) (tmp := .x12) (x := i) (by decide) (by rw [u₄.gpr, u₃.other _ (by decide),
    u₂.other _ (by decide), u₁.other _ (by decide), hr21, add0]) fun t₅ h₅ g₅ sp₅ m₅ rd₅ wr₅ => ?_
  refine wp_add fun t₆ u₆ => ?_
  have hm₆ : t₆.mem = t.mem := by rw [u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hg₆ : ∀ g ∉ TMP, t₆.gpr g = t.gpr g := fun g hg => by
    rw [u₆.other _ (nt hg .x11), g₅ _ (nt hg .x11) (nt hg .x12), hg₄ _ (nt hg .x9) (nt hg .x10) (nt hg .x11)]
  have hb₆ : Base hE t₆ := hb.regs hm₆ (by rw [u₆.rd, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₆.sp, sp₅, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
    fun g h' => hg₆ g (br_tmp h')
  have hsi : t₆.gpr .x11 = sig + BitVec.ofNat 64 (i * p.n) := by
    rw [u₆.gpr, h₅, g₅ _ (by decide) (by decide), hg₄ _ (by decide) (by decide) (by decide), hb.x24, BitVec.add_comm]
  have hdx₆ : t₆.gpr .x10 = BitVec.ofNat 64 j ^^^ D := by
    rw [u₆.other _ (by decide), g₅ _ (by decide) (by decide), hdx]
  have hD32 : D.toNat < 2 ^ 32 := by rw [hD]; omega_using [hdig]
  refine WP.mono (wp_range_flatMap 4 (P := fun K u => Base hE u ∧
      (∀ g, g ≠ .x12 → g ≠ .x13 → g ≠ .x14 → u.gpr g = t₆.gpr g) ∧ (∀ k < 4, la p u.mem S k 32 p.n = la p t.mem S k 32 p.n) ∧
      sigC p u.mem sig i = (if ∃ k < K, kp + k = idx ∧ j = D.toNat then wotsChainAt p skSeed pkSeed a16 idx i j
        else sigC p t.mem sig i) ∧ Frame [⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩] t.mem u.mem)
    ⟨hb₆, fun _ _ _ _ => rfl, fun k _ => by rw [hm₆], by
      rw [ite_eq_right (fun ⟨k, hk, _⟩ => absurd hk (by omega_using [])), hm₆],
      by rw [hm₆]; exact Frame.refl _ _⟩ fun K hK u hu => ?_) fun u hu => ?_
  · refine WP.mono (capLane_ok hE hz (D := D) (i := i) (j := j) hK hi (by omega_using [hj]) hD32 hu.1
      (by rw [hu.2.1 _ (by decide) (by decide) (by decide), hdx₆])
      (by rw [hu.2.1 _ (by decide) (by decide) (by decide), hsi])) fun u' hu' => ?_
    have hkeep : ∀ k < 4, la p u'.mem S k 32 p.n = la p u.mem S k 32 p.n := fun k hk =>
      bytesAt_frame hu'.2.2.2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hE.dsig (o := i * p.n) (l := p.n) (a := Layout.laneA k + p.n + 32) (m := p.n) (by omega_using [hlen])
          (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])).symm) (by omega_using [hn])
    refine ⟨hu'.1, fun g h₁ h₂ h₃ => by rw [hu'.2.1 g h₁ h₂ h₃, hu.2.1 g h₁ h₂ h₃],
      fun k hk => by rw [hkeep k hk, hu.2.2.1 k hk], ?_, hu.2.2.2.2.trans hu'.2.2.2⟩
    rw [hu'.2.2.1]
    by_cases c : kp + K = idx ∧ j = D.toNat
    · rw [ite_eq_left c, ite_eq_left ⟨K, by omega_using [], c⟩, hu.2.2.1 K hK, hl K hK, cv, c.1]
    · rw [ite_eq_right c, hu.2.2.2.1]
      have e : (∃ k < K + 1, kp + k = idx ∧ j = D.toNat) ↔ (∃ k < K, kp + k = idx ∧ j = D.toNat) :=
        ⟨fun ⟨k, hk, h⟩ => ⟨k, by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h' | h'
          · exact h'
          · subst h'; exact absurd h c, h⟩, fun ⟨k, hk, h⟩ => ⟨k, by omega_using [hk], h⟩⟩
      simp only [e]
  · refine ⟨hu.1, fun g hg => by rw [hu.2.1 g (nt hg .x12) (nt hg .x13) (nt hg .x14), hg₆ g hg], ?_, hu.2.2.2.2⟩
    rw [hu.2.2.2.1]
    have e : (∃ k < 4, kp + k = idx ∧ j = D.toNat) ↔ (InR kp idx ∧ j = digitAt σ.mem S i) := by
      rw [hD]
      exact ⟨fun ⟨k, hk, h₁, h₂⟩ => ⟨⟨by omega_using [h₁], by omega_using [h₁, hk]⟩, h₂⟩,
        fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨idx - kp, by omega_using [h₁, h₂], by omega_using [h₁], h₃⟩⟩
    simp only [e]

/-! ## What a chain changes -/

/-- What a chain changes, but the lanes of `B`. -/
def AZ (p : Params) (S sig : Addr) (i : Nat) : List Region :=
  (List.range 4).map (laneR p S) ++ [⟨S, workUsed⟩, ⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩]

theorem laneR_AZ {k : Nat} (hk : k < 4) (S sig : Addr) (i : Nat) : laneR p S k ∈ AZ p S sig i := by
  simp only [AZ, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl ⟨k, hk, rfl⟩

theorem frame_AZ {rs : List Region} {m m' : Mem} {S sig : Addr} {i : Nat} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ R ∈ AZ p S sig i, Region.Sub r R) : Frame (AZ p S sig i) m m' := hf.sub hs

theorem sub_AZ_lanes {S sig : Addr} {i : Nat} :
    ∀ r ∈ (List.range 4).map (laneR p S), ∃ R ∈ AZ p S sig i, Region.Sub r R := by
  intro r hr
  exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

theorem sub_AZ_sig {S sig : Addr} {i : Nat} :
    ∀ r ∈ [(⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ : Region)], ∃ R ∈ AZ p S sig i, Region.Sub r R := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, by simp [AZ], fun _ h => h⟩

/-- `thash4` on `A` changes only `AZ`. -/
theorem sub_AZ_t4 (hz : Sz p) {S sig : Addr} {i : Nat} :
    ∀ r ∈ t4ch p.n S 3136 128, ∃ R ∈ AZ p S sig i, Region.Sub r R := by
  have hn := hz.n32
  intro r hr
  simp only [t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl
  · refine ⟨_, laneR_AZ hj S sig i, ?_⟩
    have e := la_sub (p := p) (S := S) (k := j) (o := 32) (l := p.n) (by omega_using []) (by omega_using [])
    rwa [laneA_eq, show 3136 + 128 * j + p.n + 32 = 3136 + j * 128 + p.n + 32 by omega_using []] at e
  · exact ⟨_, by simp [AZ], fun _ h => h⟩

theorem lenN {i : Nat} (hi : i < p.len) : i * p.n + p.n ≤ p.len * p.n := by
  have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this

/-- A range of the lanes of `B` is apart from `AZ`. -/
theorem B_AZ (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {a l i : Nat} (h₁ : 3648 ≤ a)
    (h₂ : a + l ≤ 12480) (hi : i < p.len) : ∀ r ∈ AZ p S sig i, Region.Disjoint ⟨at' S a, l⟩ r := by
  have hn := hz.n32
  have hlen := lenN hi
  intro r hr
  simp only [AZ, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl
  · exact Entry.dscr (Or.inr (by rw [laneA_eq]; omega_using [hk, hn, h₁])) (by omega_using [h₂])
      (by rw [laneA_eq]; omega_using [hk, hn])
  · exact Offset.disjoint_base S (by simp only [workUsed]; omega_using [h₁]) (by omega_using [h₂])
  · exact (hE.dsig (o := i * p.n) (l := p.n) (by omega_using [hlen]) (by rw [oSigTmp_eq]; omega_using [h₂])).symm

/-- Another chain of the signature is apart from `AZ`. -/
theorem sig_AZ (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {i i' : Nat} (hi : i < p.len)
    (hi' : i' < p.len) (hne : i' ≠ i) :
    ∀ r ∈ AZ p S sig i, Region.Disjoint ⟨sig + BitVec.ofNat 64 (i' * p.n), p.n⟩ r := by
  have hn := hz.n32
  have hfit := hE.reg.out_fit; simp only at hfit
  intro r hr
  simp only [AZ, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl
  · exact hE.dsig (lenN hi') (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])
  · exact (hE.reg.out_scr.sub_left (Offset.sub_base sig (lenN hi'))).sub_right
      (Region.sub_prefix (by rw [oSigTmp_eq]; decide))
  · have hc : i' * p.n + p.n ≤ i * p.n ∨ i * p.n + p.n ≤ i' * p.n := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · left; have := Nat.mul_le_mul_right p.n (show i' + 1 ≤ i by omega_using [h])
        rwa [Nat.add_mul, Nat.one_mul] at this
      · right; have := Nat.mul_le_mul_right p.n (show i + 1 ≤ i' by omega_using [h])
        rwa [Nat.add_mul, Nat.one_mul] at this
    exact Offset.disjoint sig hc (by omega_using [lenN hi', hfit]) (by omega_using [lenN hi, hfit])

/-! ## Updates of a lane's address -/

theorem LaneA.set16 (hz : Sz p) {m m' : Mem} {S : Addr} {k ty κ c h ty' : Nat} {M : List Byte} (hk : k < 4)
    (hl : LaneA p m S k ty κ c h M) (hf : Frame [⟨at' S (Layout.laneA k + p.n + 16), 4⟩] m m')
    (hv : la p m' S k 16 4 = toByte ty' 4) : LaneA p m' S k ty' κ c h M := by
  have hn := hz.n32
  have K := fun {o₂ l₂ : Nat} (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ p.n + 32) (h : 16 + 4 ≤ o₂) =>
    la_keep hz (o₁ := 16) (l₁ := 4) (o₂ := o₂) (l₂ := l₂) hf hk hk (by omega_using []) (by omega_using [])
      h₂ h₂' (Or.inr (Or.inl h))
  exact ⟨hv, by rw [K (by omega_using []) (by omega_using [hn]) (by omega_using []), hl.f20],
    by rw [K (by omega_using []) (by omega_using [hn]) (by omega_using []), hl.f24],
    by rw [K (by omega_using []) (by omega_using [hn]) (by omega_using []), hl.f28],
    by rw [K (by omega_using []) (by omega_using []) (by omega_using []), hl.msg]⟩

theorem LaneA.set28 (hz : Sz p) {m m' : Mem} {S : Addr} {k ty κ c h h' : Nat} {M : List Byte} (hk : k < 4)
    (hl : LaneA p m S k ty κ c h M) (hf : Frame [⟨at' S (Layout.laneA k + p.n + 28), 4⟩] m m')
    (hv : la p m' S k 28 4 = toByte h' 4) : LaneA p m' S k ty κ c h' M := by
  have hn := hz.n32
  have K := fun {o₂ l₂ : Nat} (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ p.n + 32) (h : 28 + 4 ≤ o₂ ∨ o₂ + l₂ ≤ 28) =>
    la_keep hz (o₁ := 28) (l₁ := 4) (o₂ := o₂) (l₂ := l₂) hf hk hk (by omega_using []) (by omega_using [hn])
      h₂ h₂' (Or.inr h)
  exact ⟨by rw [K (by omega_using []) (by omega_using [hn]) (Or.inr (by omega_using [])), hl.f16],
    by rw [K (by omega_using []) (by omega_using [hn]) (Or.inr (by omega_using [])), hl.f20],
    by rw [K (by omega_using []) (by omega_using [hn]) (Or.inr (by omega_using [])), hl.f24], hv,
    by rw [K (by omega_using []) (by omega_using []) (Or.inl (by omega_using [])), hl.msg]⟩

/-- A frame within lane `k` keeps the other lanes. -/
theorem LaneA.keep' (hz : Sz p) {m m' : Mem} {S : Addr} {k k' ty κ c h o l : Nat} {M : List Byte}
    (hl : LaneA p m S k' ty κ c h M) (hf : Frame [⟨at' S (Layout.laneA k + p.n + o), l⟩] m m') (hk : k < 4)
    (hk' : k' < 4) (hne : k ≠ k') (h₁ : 16 ≤ o) (h₂ : o + l ≤ p.n + 32) : LaneA p m' S k' ty κ c h M :=
  hl.keep hz (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, la_sub h₁ h₂⟩) hk hk' hne

/-- `thash4` on `A` leaves the addresses of the lanes. -/
theorem t4_fields (hz : Sz p) {m m' : Mem} (hf : Frame (t4ch p.n S 3136 128) m m') {k o : Nat} (hk : k < 4)
    (h₁ : 16 ≤ o) (h₂ : o ≤ 28) : la p m' S k o 4 = la p m S k o 4 := by
  have hn := hz.n32
  refine bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl
  · refine Entry.dscr ?_ (by rw [laneA_eq]; omega_using [hk, hn, h₂]) (by omega_using [hj, hn])
    rw [laneA_eq]
    rcases Nat.lt_or_ge j k with h | h
    · right; omega_using [h, h₁, hn]
    · rcases Nat.lt_or_ge k j with h' | h'
      · left; omega_using [h', h₂, hn]
      · left; have : j = k := by omega_using [h, h']
        subst this; omega_using [h₂]
  · exact Offset.disjoint_base S (by rw [laneA_eq]; simp only [workUsed]; omega_using []) (by rw [laneA_eq]; omega_using [hk, hn, h₂])

/-- The signature's chains are apart from the lanes of `A` and from what `thash4` changes. -/
theorem sig_lanes (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {m m' : Mem} {i : Nat}
    (hi : i < p.len) (hf : Frame ((List.range 4).map (laneR p S)) m m') : sigC p m' sig i = sigC p m sig i := by
  have hn := hz.n32
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hn])
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
  exact hE.dsig (lenN hi) (by rw [laneA_eq, oSigTmp_eq]; have := List.mem_range.mp hk; omega_using [this, hn])

theorem sig_t4 (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p)
    {o st : Nat} (hlo : Lanes o st) {m m' : Mem} {i : Nat} (hi : i < p.len)
    (hf : Frame (t4ch p.n S o st) m m') : sigC p m' sig i = sigC p m sig i := by
  have hn := hz.n32
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hn])
  simp only [t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl
  · exact hE.dsig (lenN hi) (by rw [oSigTmp_eq]; rcases hlo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega_using [hj, hn])
  · exact (hE.reg.out_scr.sub_left (Offset.sub_base sig (lenN hi))).sub_right
      (Region.sub_prefix (by rw [oSigTmp_eq]; decide))

/-! ## The head of a chain -/

/-- Before step `j` of chain `i`, from the memory `m₀` at the chain's start. -/
structure StepInv (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (m₀ : Mem) (i j : Nat) (t : State) : Prop where
  base : Base hE t
  vk : VK t σ
  x21 : t.gpr .x21 = BitVec.ofNat 64 i
  x22 : t.gpr .x22 = BitVec.ofNat 64 j
  lanes : ∀ k < 4, ∃ h, LaneA p t.mem S k WOTS_HASH (kp + k) i h (cv p skSeed pkSeed a16 kp k i j)
  fr : Frame (AZ p S sig i) m₀ t.mem
  sigc : sigC p t.mem sig i = if InR kp idx ∧ digitAt σ.mem S i < j then
    wotsChainAt p skSeed pkSeed a16 idx i (digitAt σ.mem S i) else sigC p m₀ sig i

theorem kv_prfLanes (L : Layout) : (Wots.prfLanes L).all keepsV = true :=
  kv_flatMap 4 fun k => by
    simp only [Wots.prfLane, List.all_append, kv_setField _ _ (show 5 < 65536 by decide),
      kv_setField _ _ (show 0 < 65536 by decide), kv_setFieldR, kv_copyWords, Bool.and_self]

/-- The private key values' addresses and messages, the type `WOTS_PRF`. -/
theorem prfs_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {i : Nat} (hi : i < p.len)
    {t₀ : State} (hb : Base hE t₀) (hr21 : t₀.gpr .x21 = BitVec.ofNat 64 i)
    (h20 : ∀ k < 4, la p t₀.mem S k 20 4 = toByte (kp + k) 4) :
    WP isa (.block (Wots.prfLanes (L p))) t₀ (fun t => (Base hE t ∧ (∀ g ∉ TMP, t.gpr g = t₀.gpr g) ∧
      (∀ k < 4, la p t.mem S k 20 4 = toByte (kp + k) 4) ∧ (∀ k < 4, LaneA p t.mem S k WOTS_PRF (kp + k) i 0 skSeed) ∧
      Frame ((List.range 4).map (laneR p S)) t₀.mem t.mem) ∧ VK t t₀) := by
  have hn := hz.n32
  have hi32 : i < 2 ^ 32 := by have := hz.len; omega_using [hi, this, hn]
  have hlR : ∀ {k : Nat}, k < 4 → laneR p S k ∈ (List.range 4).map (laneR p S) := fun hk =>
    List.mem_map.mpr ⟨_, List.mem_range.mpr hk, rfl⟩
  refine wp_vk (kv_prfLanes _) ?_
  refine WP.mono (wp_range_flatMap 4 (P := fun j t => Base hE t ∧ (∀ g ∉ TMP, t.gpr g = t₀.gpr g) ∧
      (∀ k < 4, la p t.mem S k 20 4 = toByte (kp + k) 4) ∧ (∀ k < j, LaneA p t.mem S k WOTS_PRF (kp + k) i 0 skSeed) ∧
      Frame ((List.range 4).map (laneR p S)) t₀.mem t.mem)
    ⟨hb, fun _ _ => rfl, h20, fun _ h => absurd h (by omega_using []), Frame.refl _ _⟩ fun j hj t ht => ?_)
    fun t₁ ht₁ hvk => ⟨ht₁, hvk⟩
  · refine WP.mono (prfLane_ok hE hz hj hi32 ht.1 (by rw [ht.2.1 _ (by decide), hr21])) fun t' h => ?_
    obtain ⟨b', g', y16, y24, y28, ym, y20, f'⟩ := h
    refine ⟨b', fun g hg => by rw [g' g hg, ht.2.1 g hg], fun k hk => ?_, fun k hk => ?_,
      ht.2.2.2.2.trans (f'.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hlR hj)⟩
    · by_cases e : k = j
      · subst e; rw [y20, ht.2.2.1 k hk]
      · rw [la_keep hz (o₁ := 16) (f'.sub fun r hr => ⟨_, hr, fun _ h => h⟩) hj hk (by omega_using [])
          (by omega_using []) (by omega_using []) (by omega_using [hn]) (Or.inl (Ne.symm e)), ht.2.2.1 k hk]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact (ht.2.2.2.1 k hk').keep hz f' hj (by omega_using [hk', hj]) (by omega_using [hk'])
      · exact ⟨y16, by rw [y20, ht.2.2.1 _ hj], y24, y28, ym⟩

theorem kv_hashType (L : Layout) : (Wots.hashType L).all keepsV = true := by
  simp only [Wots.hashType, List.all_append, kv_flatMap 4 fun k => kv_setField _ _ (show 0 < 65536 by decide),
    Bool.true_and]; rfl

theorem preserved_x21 : Reg.x21 ∈ preserved := by decide
theorem preserved_x22 : Reg.x22 ∈ preserved := by decide

/-- The private key values, `PRF` of them, and the type `WOTS_HASH`. -/
theorem chainHead_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) {i : Nat} (hi : i < p.len) {t₀ : State} (hb : Base hE t₀)
    (hvk : VK t₀ σ) (hr21 : t₀.gpr .x21 = BitVec.ofNat 64 i)
    (h20 : ∀ k < 4, la p t₀.mem S k 20 4 = toByte (kp + k) 4) {X : Prog isa} {Q : State → Prop}
    (kk : ∀ t, StepInv hE t₀.mem i 0 t → WP isa X t Q) :
    WP isa (.seq (.block (Wots.prfLanes (L p))) (.seq (thashCall (L p) name T.code Layout.oA Layout.strideA
      (2 * (L p).n + 32)) (.seq (.block (Wots.hashType (L p))) X))) t₀ Q := by
  have hn := hz.n32
  have hkp := hE.kp_lt hz
  have h16 := a16_length (hE.env)
  have hlR : ∀ {k : Nat}, k < 4 → laneR p S k ∈ (List.range 4).map (laneR p S) := fun hk =>
    List.mem_map.mpr ⟨_, List.mem_range.mpr hk, rfl⟩
  refine WP.seq (WP.mono (prfs_ok hE hz hi hb hr21 h20) fun t₁ ⟨ht₁, hvk₁⟩ => ?_)
  obtain ⟨hb₁, hg₁, _, hl₁, hf₁⟩ := ht₁
  refine WP.seq (tcall_ok hE hz T name (o := 3136) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
    (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) hb₁
    fun t₂ hb₂ hg₂ hvk₂ hout hf₂ => ?_)
  have hl₂ : ∀ k < 4, LaneA p t₂.mem S k WOTS_PRF (kp + k) i 0 (cv p skSeed pkSeed a16 kp k i 0) := fun k hk => by
    have l := hl₁ k hk
    refine ⟨by rw [t4_fields hz hf₂ hk (by decide) (by decide)]; exact l.f16,
      by rw [t4_fields hz hf₂ hk (by decide) (by decide)]; exact l.f20,
      by rw [t4_fields hz hf₂ hk (by decide) (by decide)]; exact l.f24,
      by rw [t4_fields hz hf₂ hk (by decide) (by decide)]; exact l.f28, ?_⟩
    have e := hout k hk
    rw [show 3136 + k * 128 = Layout.laneA k by rw [laneA_eq]; omega_using [], laneA_msg (hb₁.env hz) hk l] at e
    rw [cv, chainAt_zero hz h16 (by omega_using [hkp, hk])]
    exact e
  refine WP.seq (wp_vk (kv_hashType _) ?_)
  simp only [Wots.hashType]
  refine WP.block_append (WP.mono (wp_range_flatMap 4 (P := fun j t => Base hE t ∧
      (∀ g ∉ TMP, t.gpr g = t₂.gpr g) ∧
      (∀ k < 4, (k < j → LaneA p t.mem S k WOTS_HASH (kp + k) i 0 (cv p skSeed pkSeed a16 kp k i 0)) ∧
        (j ≤ k → LaneA p t.mem S k WOTS_PRF (kp + k) i 0 (cv p skSeed pkSeed a16 kp k i 0))) ∧
      Frame ((List.range 4).map (laneR p S)) t₂.mem t.mem)
    ⟨hb₂, fun _ _ => rfl, fun k hk => ⟨fun h => absurd h (by omega_using []), fun _ => hl₂ k hk⟩, Frame.refl _ _⟩
    fun j hj t ht => ?_) fun t₃ ht₃ => ?_)
  · simp only [Layout.adrsOff]
    rw [← List.append_nil (setField .x19 (Layout.laneA j + p.n + 16) 0)]
    refine setField_base hE ht.1 (tailA_of hz hj (by decide) (by decide)) (laneA_al hz (by decide)) (by decide)
      fun t' b' g' y' f' => ?_
    refine WP.block_nil ⟨b', fun g hg => by rw [g' g (nt hg .x9), ht.2.1 g hg], fun k hk => ⟨fun hk' => ?_, fun hk' => ?_⟩,
      ht.2.2.2.trans (frame_cat f' (Frame.refl [] _) |>.sub fun r hr => by
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, hlR hj, la_sub (by omega_using []) (by omega_using [hn])⟩)⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
      · exact ((ht.2.2.1 k hk).1 h').keep' hz f' hj hk (by omega_using [h']) (by omega_using []) (by omega_using [hn])
      · exact ((ht.2.2.1 k hk).2 (Nat.le_refl _)).set16 hz hk f' y'
    · exact ((ht.2.2.1 k hk).2 (by omega_using [hk'])).keep' hz f' hj hk (by omega_using [hk']) (by omega_using [])
        (by omega_using [hn])
  refine wp_movz fun t₄ u₄ => WP.block_nil fun hvk₄ => kk t₄ ?_
  obtain ⟨hb₃, hg₃, hl₃, hf₃⟩ := ht₃
  have hf : Frame ((List.range 4).map (laneR p S)) t₃.mem t₄.mem := by rw [u₄.mem]; exact Frame.refl _ _
  refine ⟨hb₃.regs u₄.mem u₄.rd u₄.wr u₄.sp fun g hg => u₄.other g (ne_of_mem hg (by decide)),
    VK.trans hvk₄ (VK.trans hvk₂ (VK.trans hvk₁ hvk)),
    by rw [u₄.other _ (by decide), hg₃ _ (by decide), hg₂ _ preserved_x21 (by decide), hg₁ _ (by decide), hr21],
    by rw [u₄.gpr]; rfl, fun k hk => ⟨0, by rw [u₄.mem]; exact (hl₃ k hk).1 hk⟩,
    (((frame_AZ hf₁ sub_AZ_lanes).trans (frame_AZ hf₂ (sub_AZ_t4 hz))).trans (frame_AZ hf₃ sub_AZ_lanes)).trans
      (frame_AZ hf sub_AZ_lanes), ?_⟩
  rw [ite_eq_right (fun h => absurd h.2 (by omega_using [])),
    sig_lanes hE hz hi hf, sig_lanes hE hz hi hf₃, sig_t4 hE hz (Or.inl ⟨rfl, rfl⟩) hi hf₂, sig_lanes hE hz hi hf₁]

/-! ## A step of the chains -/

theorem sub_ne_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = !decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := fun e => h ((ofNat_eq_iff ha hb).mp (by
      have := congrArg (· + BitVec.ofNat 64 b) e
      rw [BitVec.sub_add_cancel] at this; exact this.trans (by simp)))
    rw [decide_eq_false h]; simpa using this

/-- A loop's condition, `x9 ≠ 0`, for `x9 = a - b`. -/
theorem eval_nz {s : State} {a b : Nat} (h : s.gpr .x9 = BitVec.ofNat 64 a - BitVec.ofNat 64 b) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) : isa.eval (.nonzero .x .x9) s = some (!decide (a = b)) := by
  show some ((s.gpr .x9).setWidth 64 != 0) = _
  rw [BitVec.setWidth_eq, h, sub_ne_zero ha hb]

theorem sig_step (P : Prop) [Decidable P] {d j : Nat} (f : Nat → List Byte) (Y : List Byte) :
    (if P ∧ j = d then f j else if P ∧ d < j then f d else Y) = if P ∧ d < j + 1 then f d else Y := by
  by_cases hP : P
  · by_cases h₁ : j = d
    · subst h₁; simp [hP]
    · by_cases h₂ : d < j
      · simp [hP, h₁, h₂, show d < j + 1 by omega_using [h₂]]
      · simp [hP, h₁, h₂, show ¬ d < j + 1 by omega_using [h₁, h₂]]
  · simp [hP]

theorem kv_captureLane (L : Layout) (k : Nat) : (Wots.captureLane L k).all keepsV = true := by
  rw [captureLane_eq]; simp only [List.all_append, kv_selWords]; rfl

theorem kv_capture (L : Layout) : (Wots.capture L).all keepsV = true := by
  rw [captureLanes_tail]
  simp only [List.all_append, kv_mulN, kv_flatMap 4 (kv_captureLane L)]
  rfl

theorem kv_hashAdrs (L : Layout) : (Wots.hashAdrs L).all keepsV = true := kv_flatMap 4 fun _ => kv_setFieldR _ _ _

/-- A step's capture and hash addresses `j`. -/
theorem stepPre_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {m₀ : Mem} {i j : Nat}
    (hi : i < p.len) (hj : j < 15) {t : State} (h : StepInv hE m₀ i j t) :
    WP isa (.block (Wots.capture (L p) ++ Wots.hashAdrs (L p))) t (fun t₂ => ∃ t₁ : State,
      (Base hE t₁ ∧ (∀ g ∉ TMP, t₁.gpr g = t.gpr g) ∧
        sigC p t₁.mem sig i = (if InR kp idx ∧ j = digitAt σ.mem S i then
          wotsChainAt p skSeed pkSeed a16 idx i j else sigC p t.mem sig i) ∧
        Frame [⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩] t.mem t₁.mem) ∧
      (Base hE t₂ ∧ (∀ g ∉ TMP, t₂.gpr g = t₁.gpr g) ∧
        (∀ k < 4, LaneA p t₂.mem S k WOTS_HASH (kp + k) i j (cv p skSeed pkSeed a16 kp k i j)) ∧
        Frame ((List.range 4).map (laneR p S)) t₁.mem t₂.mem) ∧ VK t₂ t) := by
  have hn := hz.n32
  have hlR : ∀ {k : Nat}, k < 4 → laneR p S k ∈ (List.range 4).map (laneR p S) := fun hk =>
    List.mem_map.mpr ⟨_, List.mem_range.mpr hk, rfl⟩
  refine wp_vk (by rw [List.all_append, kv_capture, kv_hashAdrs]; rfl) ?_
  refine WP.block_append (WP.mono (capture_ok hE hz hi (by omega_using [hj]) h.base h.x21 h.x22 fun k hk => by
      obtain ⟨_, l⟩ := h.lanes k hk; exact l.msg) fun t₁ ⟨hb₁, hg₁, hs₁, hf₁⟩ => ?_)
  have hl₁ : ∀ k < 4, ∃ h', LaneA p t₁.mem S k WOTS_HASH (kp + k) i h' (cv p skSeed pkSeed a16 kp k i j) := by
    intro k hk
    obtain ⟨h', l⟩ := h.lanes k hk
    have e : ∀ o l, 16 ≤ o → o + l ≤ p.n + 32 → la p t₁.mem S k o l = la p t.mem S k o l := fun o l h₁ h₂ =>
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hE.dsig (o := i * p.n) (l := p.n) (by omega_using [lenN hi])
          (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn, h₂])).symm) (by omega_using [h₂, hn])
    exact ⟨h', by rw [e 16 4 (by decide) (by omega_using [hn])]; exact l.f16,
      by rw [e 20 4 (by decide) (by omega_using [hn])]; exact l.f20, by rw [e 24 4 (by decide) (by omega_using [hn])]; exact l.f24,
      by rw [e 28 4 (by decide) (by omega_using [hn])]; exact l.f28, by rw [e 32 p.n (by decide) (by omega_using [])]; exact l.msg⟩
  have hbp₁ : t₁.gpr .x22 = BitVec.ofNat 64 j := by rw [hg₁ _ (by decide), h.x22]
  have hj32 : (t₁.gpr .x22).toNat < 2 ^ 32 := by rw [hbp₁]; exact toNat_lt_of (by omega_using [hj])
  have hjv : (t₁.gpr .x22).toNat = j := by rw [hbp₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj])]
  simp only [Wots.hashAdrs]
  refine WP.mono (wp_range_flatMap 4 (P := fun j' u => Base hE u ∧ (∀ g ∉ TMP, u.gpr g = t₁.gpr g) ∧
      (∀ k < 4, (k < j' → LaneA p u.mem S k WOTS_HASH (kp + k) i j (cv p skSeed pkSeed a16 kp k i j)) ∧
        (j' ≤ k → ∃ h', LaneA p u.mem S k WOTS_HASH (kp + k) i h' (cv p skSeed pkSeed a16 kp k i j))) ∧
      Frame ((List.range 4).map (laneR p S)) t₁.mem u.mem)
    ⟨hb₁, fun _ _ => rfl, fun k hk => ⟨fun h' => absurd h' (by omega_using []), fun _ => hl₁ k hk⟩, Frame.refl _ _⟩
    fun j' hj' u hu => ?_) fun t₂ ht₂ hvk₂ => ⟨t₁, ⟨hb₁, hg₁, hs₁, hf₁⟩,
      ⟨ht₂.1, ht₂.2.1, fun k hk => (ht₂.2.2.1 k hk).1 hk, ht₂.2.2.2⟩, hvk₂⟩
  · simp only [Layout.adrsOff]
    rw [← List.append_nil (setFieldR .x19 (Layout.laneA j' + p.n + 28) .x22)]
    refine setFieldR_base hE hu.1 (tailA_of hz hj' (by decide) (by decide)) (laneA_al hz (by decide))
      (by rw [hu.2.1 _ (by decide)]; exact hj32) fun u' b' g' y' f' => ?_
    rw [hu.2.1 _ (by decide), hjv] at y'
    refine WP.block_nil ⟨b', fun g hg => by rw [g' g (nt hg .x9), hu.2.1 g hg], fun k hk => ⟨fun hk' => ?_, fun hk' => ?_⟩,
      hu.2.2.2.trans (frame_cat f' (Frame.refl [] _) |>.sub fun r hr => by
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, hlR hj', la_sub (by omega_using []) (by omega_using [hn])⟩)⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
      · exact ((hu.2.2.1 k hk).1 h').keep' hz f' hj' hk (by omega_using [h']) (by omega_using []) (by omega_using [hn])
      · obtain ⟨_, l⟩ := (hu.2.2.1 k hk).2 (Nat.le_refl _)
        exact l.set28 hz hk f' y'
    · obtain ⟨h', l⟩ := (hu.2.2.1 k hk).2 (by omega_using [hk'])
      exact ⟨h', l.keep' hz f' hj' hk (by omega_using [hk']) (by omega_using []) (by omega_using [hn])⟩

/-- A step: the capture, the hash addresses `j`, `F`, and `j + 1`. -/
theorem step_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) {m₀ : Mem} {i j : Nat} (hi : i < p.len) (hj : j < 15) {t : State}
    (h : StepInv hE m₀ i j t) :
    WP isa (Wots.stepBody (L p) name T.code) t (fun t' => StepInv hE m₀ i (j + 1) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 15) := by
  have hn := hz.n32
  have h16 := a16_length (hE.env)
  refine WP.seq (WP.mono (stepPre_ok hE hz hi hj h) fun t₂ ⟨t₁, ⟨hb₁, hg₁, hs₁, hf₁⟩, ht₂, hvk₂⟩ => ?_)
  have hbp₁ : t₁.gpr .x22 = BitVec.ofNat 64 j := by rw [hg₁ _ (by decide), h.x22]
  obtain ⟨hb₂, hg₂, hl₂, hf₂⟩ := ht₂
  refine WP.seq (tcall_ok hE hz T name (o := 3136) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
    (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) hb₂
    fun t₃ hb₃ hg₃ hvk₃ hout hf₃ => ?_)
  have hl₃ : ∀ k < 4, LaneA p t₃.mem S k WOTS_HASH (kp + k) i j (cv p skSeed pkSeed a16 kp k i (j + 1)) := fun k hk => by
    have l := hl₂ k hk
    refine ⟨by rw [t4_fields hz hf₃ hk (by decide) (by decide)]; exact l.f16,
      by rw [t4_fields hz hf₃ hk (by decide) (by decide)]; exact l.f20,
      by rw [t4_fields hz hf₃ hk (by decide) (by decide)]; exact l.f24,
      by rw [t4_fields hz hf₃ hk (by decide) (by decide)]; exact l.f28, ?_⟩
    have e := hout k hk
    rw [show 3136 + k * 128 = Layout.laneA k by rw [laneA_eq]; omega_using [], laneA_msg (hb₂.env hz) hk l] at e
    rw [cv, chainAt_succ hz h16]
    exact e
  refine wp_vk rfl ?_
  refine wp_addImm (by decide) fun t₄ u₄ => wp_subImm (by decide) fun t₅ u₅ => WP.block_nil fun hvk₅ => ?_
  have hbp₄ : t₄.gpr .x22 = BitVec.ofNat 64 (j + 1) := by
    rw [u₄.gpr, hg₃ _ preserved_x22 (by decide), hg₂ _ (by decide), hbp₁, ← BitVec.ofNat_add]
  have hm₅ : t₅.mem = t₃.mem := by rw [u₅.mem, u₄.mem]
  refine ⟨⟨hb₃.regs hm₅ (by rw [u₅.rd, u₄.rd]) (by rw [u₅.wr, u₄.wr]) (by rw [u₅.sp, u₄.sp]) fun g hg => by
      rw [u₅.other g (ne_of_mem hg (by decide)), u₄.other g (ne_of_mem hg (by decide))],
    VK.trans hvk₅ (VK.trans hvk₃ (VK.trans hvk₂ h.vk)),
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), hg₃ _ preserved_x21 (by decide), hg₂ _ (by decide),
      hg₁ _ (by decide), h.x21],
    by rw [u₅.other _ (by decide), hbp₄], fun k hk => ⟨j, by rw [hm₅]; exact hl₃ k hk⟩, ?_, ?_⟩, ?_⟩
  · rw [hm₅]
    exact ((h.fr.trans (frame_AZ hf₁ sub_AZ_sig)).trans (frame_AZ hf₂ sub_AZ_lanes)).trans (frame_AZ hf₃ (sub_AZ_t4 hz))
  · rw [hm₅, sig_t4 hE hz (Or.inl ⟨rfl, rfl⟩) hi hf₃, sig_lanes hE hz hi hf₂, hs₁, h.sigc]
    exact sig_step _ (fun x => wotsChainAt p skSeed pkSeed a16 idx i x) _
  · rw [u₅.gpr, hbp₄]

/-- The 15 steps of chain `i`. -/
theorem steps_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) {m₀ : Mem} {i : Nat} (hi : i < p.len) {t : State}
    (h : StepInv hE m₀ i 0 t) :
    WP isa (.loop (Wots.stepBody (L p) name T.code) (.nonzero .x .x9)) t (StepInv hE m₀ i 15) := by
  refine WP.loop (M := isa) (Inv := fun (n : Nat) (u : State) => 1 ≤ n ∧ n ≤ 15 ∧ StepInv hE m₀ i (15 - n) u)
    (fun n u hu => ?_) 15 t ⟨by decide, by decide, by rw [Nat.sub_self]; exact h⟩
  obtain ⟨h₁, h₂, hu⟩ := hu
  refine WP.mono (step_ok hE hz T name hi (by omega_using [h₁]) hu) fun u' ⟨hu', h9⟩ => ?_
  have ev := eval_nz h9 (by omega_using [h₂]) (by decide)
  by_cases e : 15 - n + 1 = 15
  · rw [e] at hu'
    exact Or.inl ⟨by rw [ev, decide_eq_true e]; rfl, hu'⟩
  · refine Or.inr ⟨by rw [ev, decide_eq_false e]; rfl, n - 1, by omega_using [h₁],
      ⟨by omega_using [e, h₁, h₂], by omega_using [h₂], ?_⟩⟩
    rw [show 15 - (n - 1) = 15 - n + 1 by omega_using [h₁, h₂, e]]; exact hu'

end VG.Proof.SlhDsa.AArch64.Wots4
