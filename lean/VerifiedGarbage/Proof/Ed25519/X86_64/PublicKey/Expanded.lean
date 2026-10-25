module

public import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified
public import VerifiedGarbage.Spec.Ed25519.ExpandedKey
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified
meta import VerifiedGarbage.Spec.Ed25519.ExpandedKey
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! # Ed25519 public-key derivation from the seed's SHA-512 digest (x86-64)

`publicKeyExpanded` is `publicKey` with its first step, `pkHash`, replaced by
`pkCopyExpanded`: the digest at the second argument is copied to `scratch + 1568`, where
`pkHash` leaves it. The rest is proven once, by `bodyFrom_ok` and `bodyFrom_pk_ct`, for
both. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Ed25519 (bytesAt_of_words publicKey_of_sha512_eq sha512_length)

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem seed_contains (hL : L.Ok) (h64 : L.seedLen = 64) {i : Nat} (hi : i < 8) :
    L.SEED.Contains (L.seed + BitVec.ofNat 64 (8 * i)) 8 := by
  have hn := hL.ns
  show Region.Contains ⟨L.seed, L.seedLen⟩ _ 8
  rw [h64] at hn ⊢
  have := Offset.contains L.seed (d := 8 * i) (n := 8) (e := 0) (k := 64) (by omega) (by omega) (by decide)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- The words of the digest are those of the caller's memory. -/
theorem seed_word (hL : L.Ok) (h64 : L.seedLen = 64) {t : State} (hc : Ctx L g mx m₀ t) {i : Nat}
    (hi : i < 8) :
    t.mem.readW (L.seed + BitVec.ofNat 64 (8 * i)) 64 = m₀.readW (L.seed + BitVec.ofNat 64 (8 * i)) 64 := by
  refine hc.frame.readW (r := L.SEED) (seed_contains hL h64 hi) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hL.os.symm
  · exact hL.sc
  · exact hL.ks.symm

/-- Code that writes only caller-saved registers and a word of `scratch`. -/
theorem Ctx.storeScr (hL : L.Ok) {t t' : State} (hc : Ctx L g mx m₀ t) {e : Nat} (he : e + 8 ≤ 8192)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hmx : t'.mxcsr = t.mxcsr) (hsy : t'.syms = t.syms)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.scr + BitVec.ofNat 64 e, 8⟩] t.mem t'.mem) : Ctx L g mx m₀ t' := by
  have keep : ∀ d, 48 ≤ d → d + 8 ≤ 72 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (d := d) (n := 8) (by omega) he) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 48 (by omega) (by omega)).trans hc.pScr, (keep 56 (by omega) (by omega)).trans hc.pSeed,
    (keep 64 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, Offset.sub_base _ he⟩), by rw [hsy]; exact hc.sym, hc.held⟩

/-- The pointers of the copy, from the frame. -/
theorem copyPtrs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkCopyPtrs) t fun t' => Ctx L g mx m₀ t' ∧ t'.gpr .rax = L.seed ∧ t'.gpr .rcx = L.scr := by
  have h56 := hc.inFr (d := 56) (by omega) (by omega)
  have h48 := hc.inFr (d := 48) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkCopyPtrs, fSeed, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    hc.rsp, add_add, Nat.reduceAdd, h56, h48, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', hc.pSeed, hc.pScr, reduceCtorEq, ite_false]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial⟩

/-- One word of the digest: loaded at `rax + 8 i`, stored at `rcx + 1568 + 8 i`. -/
theorem copy_word (hL : L.Ok) (h64 : L.seedLen = 64) {t : State} (hc : Ctx L g mx m₀ t)
    (ha : t.gpr .rax = L.seed) (hs : t.gpr .rcx = L.scr) (i : Nat) (hi : i < 8) :
    WP isa (.block [.mov .rdx (.mem { base := .rax, disp := ((8 * i : Nat) : Int) }),
        .store { base := .rcx, disp := ((digestAt + 8 * i : Nat) : Int) } .rdx]) t
      fun t' => Ctx L g mx m₀ t' ∧ t'.gpr .rax = L.seed ∧ t'.gpr .rcx = L.scr ∧
        t'.mem = t.mem.writeW (L.scr + BitVec.ofNat 64 (1568 + 8 * i))
          (m₀.readW (L.seed + BitVec.ofNat 64 (8 * i)) 64) := by
  have hl : InRegions (t.rd ++ t.wr) (L.seed + BitVec.ofNat 64 (8 * i)) 8 :=
    ⟨L.SEED, by rw [hc.rd]; simp, seed_contains hL h64 hi⟩
  have hw : InRegions t.wr (L.scr + BitVec.ofNat 64 (1568 + 8 * i)) 8 :=
    ⟨L.SCR, by rw [hc.wr]; simp, Offset.contains_base _ (by omega) (by have := hL.nc; omega)⟩
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 (1568 + 8 * i), 8⟩] t.mem
      (t.mem.writeW (L.scr + BitVec.ofNat 64 (1568 + 8 * i)) (m₀.readW (L.seed + BitVec.ofNat 64 (8 * i)) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  apply WP.of_runBlock
  simp only [digestAt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    State.store64, ea_base, ha, hs, hl, hw, ite_true, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, Option.map_some, reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  rw [seed_word hL h64 hc hi]
  exact ⟨hc.storeScr hL (e := 1568 + 8 * i) (by omega) rfl rfl rfl rfl (by cs_tac) hf, trivial, trivial, rfl⟩

/-- The digest's first `k` words copied. -/
theorem copy_prefix (hL : L.Ok) (h64 : L.seedLen = 64) (k : Nat) (hk : k ≤ 8) {t : State}
    (hc : Ctx L g mx m₀ t) (ha : t.gpr .rax = L.seed) (hs : t.gpr .rcx = L.scr) :
    WP isa (.block ((List.range k).flatMap fun i =>
        [.mov .rdx (.mem { base := .rax, disp := ((8 * i : Nat) : Int) }),
          .store { base := .rcx, disp := ((digestAt + 8 * i : Nat) : Int) } .rdx])) t
      fun t' => Ctx L g mx m₀ t' ∧ t'.gpr .rax = L.seed ∧ t'.gpr .rcx = L.scr ∧ ∀ j < k,
        t'.mem.readW (L.scr + BitVec.ofNat 64 (1568 + 8 * j)) 64 =
          m₀.readW (L.seed + BitVec.ofNat 64 (8 * j)) 64 := by
  induction k with
  | zero => exact WP.of_runBlock ⟨t, rfl, hc, ha, hs, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun u ⟨hu, hua, hus, hw⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (copy_word hL h64 hu hua hus k (by omega)) fun w ⟨hw', hwa, hws, hm⟩ =>
      ⟨hw', hwa, hws, fun j hj => ?_⟩
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep L.scr (d := 1568 + 8 * j) (n := 8) (e := 1568 + 8 * k) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact hw j hj
    · exact Mem.readW_writeW_self64 _ _ _

/-- `pkCopyExpanded` leaves the caller's 64 bytes at `seed` at `scratch + 1568`. -/
theorem copy_ok (hL : L.Ok) (h64 : L.seedLen = 64) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa pkCopyExpanded t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1568) 64 = Spec.Ed25519.bytesAt m₀ L.seed 64 := by
  refine WP.seq (WP.mono (copyPtrs_ok hc) fun u ⟨hu, ha, hs⟩ => ?_)
  refine WP.mono (copy_prefix hL h64 8 (Nat.le_refl _) hu ha hs) fun w ⟨hw, _, _, hwd⟩ => ⟨hw, ?_⟩
  refine bytesAt_of_words fun k hk => ?_
  rw [add_add]
  exact hwd k hk

/-! ## The expanded-key entry point -/

/-- Derivation from the seed's digest at `rsi`. -/
def pkLocalE : Contract isa := pkLocalWith 64
  (fun s => ∃ seed : List Byte, seed.length = 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 64 = Spec.Sha512.sha512 seed)
  (fun s s' => ∀ seed : List Byte, seed.length = 32 →
    Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 64 = Spec.Sha512.sha512 seed →
    Spec.Ed25519.bytesAt s'.mem (s.gpr .rdi) 32 = Spec.Ed25519.publicKey seed)

theorem expanded_seed {s : State} (h : pkLocalE.pre s) :
    ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt s.mem (lay 64 s).seed 64 = Spec.Sha512.sha512 seed := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩
  exact hk

theorem publicKeyExpanded_ok {s : State} (h : pkLocalE.pre s) :
    WP isa (publicKeyExpanded bs fs) s fun s' => abiPreserved s s' ∧ pkLocalE.post s s' := by
  have hL := lay_ok h (by decide)
  have hc := push_ctx h
  obtain ⟨seed, -, hE⟩ := expanded_seed h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide) (by show 8 * 7 ≤ _; have := h.1; omega)
    (WP.mono (bodyFrom_ok hL (copy_ok hL rfl hc) hE)
      fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 7 from rfl, pop_rsp, lay_ret]
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
    show Spec.Ed25519.bytesAt (popped .rax pushRs.length u).mem (lay 64 s).out 32 = _
    rw [popped_mem, ho]
    exact publicKey_of_sha512_eq (hE.symm.trans hE')

theorem copy_ct : RelCT isa (Two fun L _ => L.seedLen = 64) pkCopyExpanded (Two fun _ _ => True) := by
  have p : RelCT isa (Two fun L _ => L.seedLen = 64) (.block pkCopyPtrs)
      (Two fun L t => L.seedLen = 64 ∧ t.gpr .rax = L.seed ∧ t.gpr .rcx = L.scr) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc h64 =>
      WP.mono (copyPtrs_ok hc) fun _ ⟨hc', ha, hs⟩ => ⟨hc', h64, ha, hs⟩
  have w : RelCT isa (Two fun L t => L.seedLen = 64 ∧ t.gpr .rax = L.seed ∧ t.gpr .rcx = L.scr)
      (.block pkCopyWords) (Two fun _ _ => True) := by
    refine two_blk [.rsp, .rax, .rcx] (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ r hr => ?_) (by taint_decide)
      fun _ _ _ _ _ hL hc ⟨h64, ha, hs⟩ =>
        WP.mono (copy_prefix hL h64 8 (Nat.le_refl _) hc ha hs) fun _ ⟨hc', _⟩ => ⟨hc', trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact rsp_two c₁ c₂
    · exact a₁.2.1.trans a₂.2.1.symm
    · exact a₁.2.2.trans a₂.2.2.symm
  exact p.seq w

theorem publicKeyExpanded_ct :
    ConstantTime isa pkLocalE.pre pkLocalE.pub (publicKeyExpanded bs fs) :=
  bodyFrom_pk_ct (by decide) copy_ct fun _ _ => rfl

/-! ## A witness, the shared contract, and the stack -/

def satSeedE : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satDigestE : List Byte := Spec.Sha512.sha512 satSeedE

/-- The witness's memory: the digest at `0x2000`, the comb's tables at `0x100000`. -/
@[irreducible] def satMemPE : Mem := fun a =>
  if 0x100000 ≤ a.toNat then constMem 0x100000 combWords a
  else if 0x2000 ≤ a.toNat ∧ a.toNat < 0x3000 then satDigestE[a.toNat - 0x2000]?.getD 0 else 0

theorem satSeedE_length : satSeedE.length = 32 := by
  simp only [satSeedE, Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem satPE_digest : Spec.Ed25519.bytesAt satMemPE 0x2000 64 = satDigestE := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigestE, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega
    unfold satMemPE
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, ha,
      show ¬ 0x100000 ≤ 0x2000 + i from by omega, show 0x2000 ≤ 0x2000 + i ∧ 0x2000 + i < 0x3000 from by omega,
      ite_false, and_self, ite_true, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem satMemPE_held : ∀ i < combWordCount,
    satMemPE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  rw [← constMem_held (0x100000 : Addr) combWords
    (by rw [Proof.Ed25519.X86_64.combWords_length]; simp only [combWordCount]; omega) i
    (by rw [Proof.Ed25519.X86_64.combWords_length]; exact hi)]
  refine Mem.readW_congr fun b hb => ?_
  unfold satMemPE
  rw [ite_eq_left_of_eq_true _ _ (eq_true ?_)]
  rw [show (0x100000 : Addr) = BitVec.ofNat 64 0x100000 from rfl, Offset.add_add, ← BitVec.ofNat_add,
    BitVec.toNat_ofNat]
  simp only [combWordCount] at hi
  omega

/-- A state satisfying the precondition. -/
def satStatePE : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemPE
  rd := [⟨0x2000, 64⟩, ⟨0x100000, 40448⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]
  syms _ := 0x100000

theorem sat_localPE : pkLocalE.pre satStatePE := by
  refine ⟨by decide, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide,
    ⟨satSeedE, satSeedE_length, satPE_digest⟩, satMemPE_held, by decide, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

/-- The shared contract's precondition, from `pkLocalE`'s. -/
theorem pkE_spec_pre {s : State} (h : pkLocalE.pre s) :
    (Spec.Ed25519.publicKeyExpandedContract (X86_64.abi.withConsts combConsts) 72).pre s := by
  obtain ⟨h72, hrd, hw, h1, h2, h3, r1, r2, r3, k1, k2, k3, f0, f1, f2, pk, held, fit, hdw⟩ := h
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Ed25519.X86_64.combWords_length]
  exact ⟨h72, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hdw _ (by simp), by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, k1, k2, k3, f0, f1, f2, pk⟩

theorem impliesE :
    pkLocalE.Implies (Spec.Ed25519.publicKeyExpandedContract (X86_64.abi.withConsts combConsts) 72) where
  pre s h := by
    sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Ed25519.X86_64.combWords_length] at h
    obtain ⟨h72, hd, hheld, hfit, hdw, hdr, hdk, ht, hw, d1, d2, d3, d4, d5, d6, d7, d8, d9, f0, f1, f2, pk⟩ := h
    refine ⟨h72, ?_, hw, d1, d2, d3, d4, d5, d6, d7, d8, d9, f0, f1, f2, pk, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
      · exact hdk
  post := by
    intro s s' _ h
    sig_post [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
      Abi.withConsts, pkLocalE, pkLocalWith]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hs⟩
  sat := ⟨_, pkE_spec_pre sat_localPE⟩

theorem publicKeyExpanded_verified :
    Verified X86_64.target (publicKeyExpanded bs fs)
      (Spec.Ed25519.publicKeyExpandedContract (X86_64.abi.withConsts combConsts) 72) :=
  Verified.of_correct (fun _ h => publicKeyExpanded_ok h) publicKeyExpanded_ct impliesE

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem publicKeyExpanded_spSafe :
    (publicKeyExpanded bs fs).all (fun i => !isa.writesSp i) = true := by
  have hb : bs.all (fun i => !isa.writesSp i) = true := base_spSafe
  simp only [publicKeyExpanded, pkBodyFrom, pkCopyExpanded, pkCopyPtrs, pkCopyWords, Code.all, hb,
    Bool.true_and]
  decide

end VG.Proof.Ed25519.X86_64.PublicKey
