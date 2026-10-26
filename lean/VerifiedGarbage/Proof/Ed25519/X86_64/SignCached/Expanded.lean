module

public import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Verified
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Verified
meta import VerifiedGarbage.Spec.Ed25519.ExpandedSign
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! # Complete Ed25519 signing with the seed's cached SHA-512 digest (x86-64)

`codeExpanded` is `code` with its first step, `hashSeed`, replaced by `copyExpanded`: the
digest at the second argument is copied to `stk 128`, where `hashSeed` leaves it. The rest is
proven once, by `bodyFrom_ok` and `bodyFrom_sign_ct`, for both. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (stk)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk ea_base add_add)
open VG.Proof.Sha512.X86_64 (Compress)
open VG.Proof.Ed25519 (bytesAt_of_words sign_of_sha512_eq sha512_length)

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem seed_contains (hL : L.Ok) (h64 : L.seedLen = 64) {i : Nat} (hi : i < 8) :
    L.SEED.Contains (L.seed + BitVec.ofNat 64 (8 * i)) 8 := by
  have hn := hL.ns
  show Region.Contains ⟨L.seed, L.seedLen⟩ _ 8
  rw [h64] at hn ⊢
  have := Offset.contains L.seed (d := 8 * i) (n := 8) (e := 0) (k := 64) (by omega) (by omega) (by decide)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- The words at `seed` are those of the caller's memory. -/
theorem seed_word (hL : L.Ok) (h64 : L.seedLen = 64) {t : State} (hc : Ctx L g mx m₀ t) {i : Nat}
    (hi : i < 8) :
    t.mem.readW (L.seed + BitVec.ofNat 64 (8 * i)) 64 = m₀.readW (L.seed + BitVec.ofNat 64 (8 * i)) 64 := by
  have hn := hL.ns
  rw [h64] at hn
  have hcon : L.SEED.Contains (L.seed + BitVec.ofNat 64 (8 * i)) 8 := seed_contains hL h64 hi
  refine hc.frame.readW (r := L.SEED) hcon ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hL.os _ (by simp [Lay.inputs])).symm
  · exact hL.sc _ (by simp [Lay.inputs])
  · exact (hL.ks _ (by simp [Lay.inputs])).symm

/-- One word of the digest: loaded at `rax + 8 i`, stored at `stk (128 + 8 i)`. -/
theorem copy_word (hL : L.Ok) (h64 : L.seedLen = 64) {t : State} (hc : Ctx L g mx m₀ t)
    (hr : t.gpr .rax = L.seed) (i : Nat) (hi : i < 8) :
    WP isa (.block [.mov .rcx (.mem { base := .rax, disp := (8 * i : Nat) }), .store (stk (128 + 8 * i)) .rcx]) t
      fun t' => Ctx L g mx m₀ t' ∧ t'.gpr .rax = L.seed ∧
        t'.mem = t.mem.writeW (L.B + BitVec.ofNat 64 (144 + 8 * i))
          (m₀.readW (L.seed + BitVec.ofNat 64 (8 * i)) 64) := by
  have hn := hL.ns
  rw [h64] at hn
  have hl : InRegions (t.rd ++ t.wr) (L.seed + BitVec.ofNat 64 (8 * i)) 8 :=
    ⟨L.SEED, by rw [hc.rd]; simp [Lay.inputs], seed_contains hL h64 hi⟩
  have hw := hc.inFrW (d := 144 + 8 * i) (by omega) (by omega)
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (144 + 8 * i), 8⟩] t.mem
      (t.mem.writeW (L.B + BitVec.ofNat 64 (144 + 8 * i)) (m₀.readW (L.seed + BitVec.ofNat 64 (8 * i)) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have e : 16 + (128 + 8 * i) = 144 + 8 * i := by omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.store64,
    ea_base, ea_stk, hc.rsp, hr, add_add, e, hw, hl, ite_true, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, Option.map_some, reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  rw [seed_word hL h64 hc hi]
  exact ⟨hc.store (d := 144 + 8 * i) (n := 8) (by omega) (by omega) rfl rfl rfl rfl (by cs_tac) hf, trivial, rfl⟩

/-- The digest's address, from the saved second argument. -/
theorem seedPtr_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block [.mov .rax (.mem (stk fSeed))]) t fun t' => Ctx L g mx m₀ t' ∧ t'.gpr .rax = L.seed := by
  have hs := hc.inFr (d := 248) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [fSeed, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, hc.rsp, add_add,
    Nat.reduceAdd, hs, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', hc.pSeed]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial⟩

/-- The digest's first `k` words copied. -/
theorem copy_prefix (hL : L.Ok) (h64 : L.seedLen = 64) (k : Nat) (hk : k ≤ 8) {t : State}
    (hc : Ctx L g mx m₀ t) (hr : t.gpr .rax = L.seed) :
    WP isa (.block ((List.range k).flatMap fun i =>
        [.mov .rcx (.mem { base := .rax, disp := (8 * i : Nat) }), .store (stk (128 + 8 * i)) .rcx])) t
      fun t' => Ctx L g mx m₀ t' ∧ t'.gpr .rax = L.seed ∧ ∀ j < k,
        t'.mem.readW (L.B + BitVec.ofNat 64 (144 + 8 * j)) 64 =
          m₀.readW (L.seed + BitVec.ofNat 64 (8 * j)) 64 := by
  induction k with
  | zero => exact WP.of_runBlock ⟨t, rfl, hc, hr, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun u ⟨hu, hur, hw⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (copy_word hL h64 hu hur k (by omega)) fun w ⟨hw', hwr, hm⟩ => ⟨hw', hwr, fun j hj => ?_⟩
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep L.B (d := 144 + 8 * j) (n := 8) (e := 144 + 8 * k) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact hw j hj
    · exact Mem.readW_writeW_self64 _ _ _

/-- `copyExpanded` leaves the caller's 64 bytes at `seed` at `stk 128`. -/
theorem copy_ok (hL : L.Ok) (h64 : L.seedLen = 64) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa copyExpanded t fun t' =>
      Ctx L g mx m₀ t' ∧ DigestReady L (Spec.Ed25519.bytesAt m₀ L.seed 64) t' := by
  refine WP.seq (WP.mono (seedPtr_ok hc) fun u ⟨hu, hr⟩ => ?_)
  refine WP.mono (copy_prefix hL h64 8 (Nat.le_refl _) hu hr) fun w ⟨hw, _, hwd⟩ => ⟨hw, ?_⟩
  refine bytesAt_of_words fun k hk => ?_
  rw [add_add]
  exact hwd k hk

/-! ## The expanded-key entry point -/

/-- Signing with the seed's digest at `rsi` and its public key at `rdx`. -/
def signLocalE : Contract isa := signLocalWith 64
  (fun s => ∃ seed : List Byte, seed.length = 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 64 = Spec.Sha512.sha512 seed ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32 = Spec.Ed25519.publicKey seed)
  (fun s t => ∀ seed : List Byte, seed.length = 32 →
    Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 64 = Spec.Sha512.sha512 seed →
    Spec.Ed25519.bytesAt t.mem (s.gpr .rdi) 64 =
      Spec.Ed25519.sign seed (Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat))

theorem expanded_key {s : State} (h : signLocalE.pre s) :
    ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt s.mem (lay 64 s).seed 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt s.mem (lay 64 s).pk 32 = Spec.Ed25519.publicKey seed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩
  exact hk

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}
open VG.Proof.Ed25519.X86_64.PublicKey (ne_cs)

theorem signE_ok (v : Compress) {s : State} (h : signLocalE.pre s) :
    WP isa (codeExpanded bs fs v.callee v.suffix) s fun s' => abiPreserved s s' ∧ signLocalE.post s s' := by
  have hL := lay_ok h (by decide)
  have hc := push_ctx h
  obtain ⟨seed, -, hE, hpk⟩ := expanded_key h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide) (by show 8 * 31 ≤ _; have := h.1; omega)
    (WP.mono (bodyFrom_ok v hL (copy_ok hL rfl hc) hL.message_bound hE hpk)
      fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 31 from rfl, add_add, lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay 64 s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · intro seed' _ hE'
    show Spec.Ed25519.bytesAt (popped .rax pushRs.length u).mem (lay 64 s).out 64 = _
    rw [popped_mem, ho]
    exact sign_of_sha512_eq (hE.symm.trans hE') _

/-- Runs whose `rax` both hold `seed` agree on it: a block reading memory at `rax` is related
by taint with `rax` public. -/
theorem two_block_rax {is : List Instr} {Φ : Lay → Mem → State → Prop}
    (hΦ : ∀ L m t, Φ L m t → t.gpr .rax = L.seed)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp, .rax]) (.block is) hc).isSome = true) :
    RelCT isa (Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rsp, .rax]) (fun _ _ ⟨_, _, c₁, c₂, f₁, f₂⟩ =>
    Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact c₁.rsp.trans c₂.rsp.symm
      · exact (hΦ _ _ _ f₁).trans (hΦ _ _ _ f₂).symm)) h

theorem copy_ct : RelCT isa (Two fun L _ _ => L.seedLen = 64) copyExpanded (Two fun _ _ _ => True) := by
  have p : RelCT isa (Two fun L _ _ => L.seedLen = 64) (.block [.mov .rax (.mem (stk fSeed))])
      (Two fun L _ t => L.seedLen = 64 ∧ t.gpr .rax = L.seed) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc h64 =>
      WP.mono (seedPtr_ok hc) fun _ ⟨hc', hr⟩ => ⟨hc', h64, hr⟩
  have w : RelCT isa (Two fun L _ t => L.seedLen = 64 ∧ t.gpr .rax = L.seed) (.block copyWords)
      (Two fun _ _ _ => True) :=
    two_wp (two_block_rax (fun _ _ _ h => h.2) (by taint_decide)) fun _ _ _ _ _ hL hc ⟨h64, hr⟩ =>
      WP.mono (copy_prefix hL h64 8 (Nat.le_refl _) hc hr) fun _ ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact p.seq w

theorem signE_ct (v : Compress) :
    ConstantTime isa signLocalE.pre signLocalE.pub (codeExpanded bs fs v.callee v.suffix) :=
  bodyFrom_sign_ct v (by decide) copy_ct fun _ _ => rfl

/-! ## A witness, the shared contract, and the stack -/

def satDigest : List Byte := Spec.Sha512.sha512 satSeed

def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0
  else if a.toNat < 0x3000 then satDigest[a.toNat - 0x2000]?.getD 0
  else satKey[a.toNat - 0x3000]?.getD 0

theorem satSeed_length : satSeed.length = 32 := by
  simp only [satSeed, Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem sat_digest : Spec.Ed25519.bytesAt satMemE 0x2000 64 = satDigest := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigest, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega, show 0x2000 + i < 0x3000 from by omega, ite_false, ite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_keyE : Spec.Ed25519.bytesAt satMemE 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x3000 + i < 0x2000 from by omega, show ¬ 0x3000 + i < 0x3000 from by omega, ite_false,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The memory of the contract's witness: `satMemE`, and the comb's tables at `0x100000`. -/
@[irreducible] def satMemTE : Mem := fun a =>
  if 0x100000 ≤ a.toNat then constMem 0x100000 Impl.Ed25519.X86_64.combWords a else satMemE a

theorem satMemTE_bytes {p : Addr} {n : Nat} (hp : p.toNat + n ≤ 0x100000) :
    Spec.Ed25519.bytesAt satMemTE p n = Spec.Ed25519.bytesAt satMemE p n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  unfold satMemTE
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  simp only [show ¬ 0x100000 ≤ (p.toNat + i) % 2 ^ 64 by omega, ite_false]

theorem satMemTE_held : ∀ i < Impl.Ed25519.X86_64.combWordCount,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.Ed25519.X86_64.combWords.getD i 0 := by
  intro i hi
  rw [← constMem_held (0x100000 : Addr) Impl.Ed25519.X86_64.combWords
    (by rw [Proof.Ed25519.X86_64.combWords_length]; simp only [Impl.Ed25519.X86_64.combWordCount]; omega) i
    (by rw [Proof.Ed25519.X86_64.combWords_length]; exact hi)]
  refine Mem.readW_congr fun b hb => ?_
  unfold satMemTE
  rw [ite_eq_left_of_eq_true _ _ (eq_true ?_)]
  rw [show (0x100000 : Addr) = BitVec.ofNat 64 0x100000 from rfl, Offset.add_add, ← BitVec.ofNat_add,
    BitVec.toNat_ofNat]
  simp only [Impl.Ed25519.X86_64.combWordCount] at hi
  omega

/-- A state satisfying the precondition. -/
def satStateTE : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000
    | .r8 => 0 | .r9 => 0x5000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemTE
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x100000, 40448⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]
  syms _ := 0x100000

theorem sat_localE : signLocalE.pre satStateTE := by
  refine ⟨by decide, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide, by decide,
    by decide, ?_, satMemTE_held, by decide, ?_⟩
  · refine ⟨satSeed, satSeed_length, ?_, ?_⟩
    · show Spec.Ed25519.bytesAt satMemTE 0x2000 64 = _
      rw [satMemTE_bytes (by decide), sat_digest]
      rfl
    · show Spec.Ed25519.bytesAt satMemTE 0x3000 32 = _
      rw [satMemTE_bytes (by decide), sat_keyE]
      rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

/-- The shared contract's precondition, from `signLocalE`'s. -/
theorem signE_spec_pre {s : State} (h : signLocalE.pre s) (hal : (s.syms Impl.Ed25519.X86_64.combSym).toNat % 64 = 0) :
    (Spec.Ed25519.signExpandedContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts) 264).pre s := by
  obtain ⟨h264, hrd, hw, o1, o2, o3, o4, k1, r1, n1, c1, c2, c3, k2, k3, k4, r2, r3, r4, k5, r5, n3, n4,
    n2, n5, pk, held, fit, hdw⟩ := h
  sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
    Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Ed25519.X86_64.combWords_length]
  exact ⟨h264, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hdw _ (by simp), hal, by rw [hrd]; rfl, hw, o1, o2, o3, o4, c1, c2, c3, r1, r2, r3, r4, r5,
    k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, pk⟩

theorem impliesE :
    signLocalE.Implies
      (Spec.Ed25519.signExpandedContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts) 264) where
  pre s h := by
    sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Ed25519.X86_64.combWords_length] at h
    obtain ⟨h264, hd, held, fit, hdw, hdr, hdk, -, ht, hw, o1, o2, o3, o4, c1, c2, c3, r1, r2, r3, r4, r5,
      k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, pk⟩ := h
    refine ⟨h264, ?_, hw, o1, o2, o3, o4, k1, r1, n1, c1, c2, c3, k2, k3, k4, r2, r3, r4, k5, r5, n3, n4,
      n2, n5, pk, held, fit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
      · exact hdk
  post := by
    intro s s' _ h
    sig_post [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
      Abi.withConsts, signLocalE, signLocalWith]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, hs⟩
  sat := ⟨satStateTE, signE_spec_pre sat_localE (by decide)⟩

theorem verifiedE (v : Compress) : Verified X86_64.target (codeExpanded bs fs v.callee v.suffix)
    (Spec.Ed25519.signExpandedContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts) 264) :=
  Verified.of_correct (fun _ h => signE_ok v h) (signE_ct v) impliesE

theorem spSafeE (v : Compress) :
    (codeExpanded bs fs v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  have hu := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe
  have hf := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe
  have hr : Impl.Ed25519.X86_64.scalarReduce.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  have hb : bs.all (fun i => !isa.writesSp i) = true := PublicKey.base_spSafe
  have hm : Impl.Ed25519.X86_64.scalarMulAdd.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  have hi : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !isa.writesSp i) = true := by
    decide +kernel
  simp only [codeExpanded, bodyFrom, copyExpanded, copyWords, hashNonce, hashChallenge, init, update, finalize,
    reduce, Impl.Ed25519.X86_64.callWith, Code.all, hu, hf, hr, hb, hm, hi, Bool.and_true]
  decide

end VG.Proof.Ed25519.X86_64.SignCached
