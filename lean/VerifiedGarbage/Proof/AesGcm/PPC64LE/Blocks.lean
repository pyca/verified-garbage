module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.Aes.Memory
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.VectorCrypto
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Rounds

/-! # Component proofs for the fused POWER8 AES-GCM bulk loop -/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Blocks
open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks (U LO MID HI T)
open VG.Proof.Gcm.PPC64LE.Vpmsum (productsWith_ok reduceWith_ok)
open VG.Proof.Gcm.Clmul (mulV)
open VG.Proof.Aes.PPC64LE.Crypto (aesState)
open VG.Impl.Gcm.Clmul (poly)

def multiplyRegs : Fin 5 → VReg
  | ⟨0, _⟩ => U | ⟨1, _⟩ => LO | ⟨2, _⟩ => MID | ⟨3, _⟩ => HI | _ => .v0

def reductionRegs : Fin 6 → VReg
  | ⟨0, _⟩ => LO | ⟨1, _⟩ => MID | ⟨2, _⟩ => HI
  | ⟨3, _⟩ => T | ⟨4, _⟩ => .v0 | _ => .v13

theorem mul_ok (d a key : VReg) (s : State)
    (ha : a ∉ [U, LO, MID, HI]) (hk : key ∉ [U, LO, MID, HI])
    (hc : s.vpr .v13 = poly ++ poly) (hz : s.vpr .v0 = 0) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.mul d a key .v0 .v13)) s fun t =>
      t.vpr d = mulV (s.vpr a) (s.vpr key) ∧ VOnly [U, LO, MID, HI, T, d] s t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.mul, WP.block_append_iff]
  refine WP.mono (productsWith_ok multiplyRegs
    (show ∀ i j : Fin 5, multiplyRegs i = multiplyRegs j → i = j from by decide)
    a key s ha hk hz) fun u ⟨hp, ho⟩ => ?_
  change (⟨u.vpr LO, u.vpr MID, u.vpr HI⟩ : VG.Proof.Gcm.Clmul.Prod) = _ at hp
  change VOnly [U, LO, MID, HI] s u at ho
  have hc' : u.vpr .v13 = poly ++ poly := (ho.v .v13 (by decide)).trans hc
  have hz' : u.vpr .v0 = 0 := (ho.v .v0 (by decide)).trans hz
  refine WP.mono (reduceWith_ok reductionRegs
    (show ∀ i j : Fin 6, reductionRegs i = reductionRegs j → i = j from by decide)
    d u hc' hz') fun t ⟨hv, hf⟩ => ?_
  change t.vpr d = VG.Proof.Gcm.Clmul.reduce ⟨u.vpr LO, u.vpr MID, u.vpr HI⟩ at hv
  change VOnly [LO, MID, HI, T, d] u t at hf
  refine ⟨?_, ?_⟩
  · rw [hv, hp]; rfl
  · exact (ho.trans hf).weaken (by
      intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h | h) | (h | h | h | h | h) <;> simp_all)

def pairedRegs : Fin 5 → VReg
  | ⟨0, _⟩ => HI | ⟨1, _⟩ => U | ⟨2, _⟩ => T | ⟨3, _⟩ => LO | _ => MID

def cipherAt (s : State) (i : Nat) : BitVec 128 := s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg i)
def hashAt (s : State) (i : Nat) : BitVec 128 :=
  VG.Proof.Gcm.Clmul.ext8 (cipherAt s i) (cipherAt s i)

def product (s : State) : VG.Proof.Gcm.Clmul.Prod := ⟨s.vpr LO, s.vpr MID, s.vpr HI⟩

theorem paired_ok (j : Fin 4) (ka kb : BitVec 128) (s : State)
    (hl : s.vpr .v8 = VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair ka kb)
    (hh : s.vpr .v9 = VG.Proof.Gcm.PPC64LE.Vpmsum.highPair ka kb) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedProductsWith
      (Impl.AesGcm.PPC64LE.Blocks.reg (2*j.val)) (Impl.AesGcm.PPC64LE.Blocks.reg (2*j.val+1))
      U T LO MID HI .v8 .v9 true)) s fun t =>
      product t = VG.Proof.Gcm.PPC64LE.Vpmsum.pairedProd
        (hashAt s (2*j.val)) (hashAt s (2*j.val+1)) ka kb ∧
      VOnly [HI, U, T, LO, MID] s t := by
  have ha : ∀ j : Fin 4, ∀ i : Fin 5,
      Impl.AesGcm.PPC64LE.Blocks.reg (2*j.val) ≠ pairedRegs i := by decide
  exact VG.Proof.Gcm.PPC64LE.Vpmsum.packedProductsWith_ok pairedRegs
    (show ∀ i k : Fin 5, pairedRegs i = pairedRegs k → i = k from by decide)
    _ _ .v8 .v9 true ka kb s (ha j) (by decide) (by decide) hl hh

private theorem zero_or128 (x : BitVec 128) : (0 : BitVec 128) ||| x = x := BitVec.zero_or

theorem packed_words (f : Nat → BitVec 32) :
    (List.range 4).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32*(3-i)))) (0 : BitVec 128) =
      f 0 ++ f 1 ++ f 2 ++ f 3 := by
  simp only [show List.range 4 = [0,1,2,3] from rfl, List.foldl_cons, List.foldl_nil,
    Nat.reduceSub, Nat.reduceMul, zero_or128, BitVec.shiftLeft_zero]
  have h := BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or
    (b := f 0) (b' := f 1) (b'' := f 2) (b''' := f 3) (w'''' := 128)
  rw [BitVec.setWidth_eq] at h
  exact h.symm

theorem word_offset (b : BitVec 32) (j : Nat) (hj : j < 4) :
    vword ((0#96) ++ b) j = if j=3 then b else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases he : j=3
  · subst j
    simp only [vword, Nat.reduceSub, Nat.mul_zero, Nat.zero_add,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
      Bool.true_and, ite_true]
  · have hge : ¬ 32*(3-j)+i < 32 := by omega
    simp only [vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
      BitVec.getLsbD_zero, he, ite_false, hge, Bool.and_false]

def wordAdd (a b : BitVec 128) : BitVec 128 :=
  (List.range 4).foldl (fun x i => x |||
    ((vword a i+vword b i).setWidth 128 <<< (32*(3-i)))) 0

theorem add_counter (a : BitVec 128) (b : BitVec 32) :
    wordAdd a ((0#96) ++ b) = a.extractLsb' 32 96 ++ (a.extractLsb' 0 32 + b) := by
  rw [wordAdd, packed_words]
  simp only [word_offset b 0 (by decide), word_offset b 1 (by decide),
    word_offset b 2 (by decide), word_offset b 3 (by decide), Nat.reduceEqDiff,
    ite_false, ite_true, BitVec.add_zero]
  simp only [vword, Nat.reduceSub, Nat.reduceMul]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]

theorem counterValue (cb : Spec.Gcm.Block) (n : Nat) :
    Nat.repeat Spec.Gcm.inc32 n cb =
      cb.extractLsb' 32 96 ++ (cb.extractLsb' 0 32 + BitVec.ofNat 32 n) := by
  rw [← VG.Proof.Aes.repeat_inc32_hi cb n, ← VG.Proof.Aes.repeat_inc32_lo cb n,
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide), BitVec.extractLsb'_eq_self]

theorem exec_add_counter (d a inc : VReg) (b : BitVec 32) (s : State)
    (hi : s.vpr inc = 0#96 ++ b) :
    exec (.vop (.add false d a inc)) s = some (s.writeV d
      ((s.vpr a).extractLsb' 32 96 ++ ((s.vpr a).extractLsb' 0 32 + b))) := by
  change some (s.writeV d (wordAdd (s.vpr a) (s.vpr inc))) = _
  rw [hi, add_counter]

theorem rawLoad_ok (d : VReg) (p offset : Reg) (s : State) (hp : p ≠ .r0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr p + s.gpr offset) 16) :
    WP isa (.block [.lxvd2x d p offset]) s fun t =>
      t.vpr d = swapDwords (s.mem.read (s.gpr p + s.gpr offset) 16) ∧ VOnly [d] s t :=
  vector_step _ d _ s (exec_lxvd2x d p offset s hp hr)

theorem rawStore_ok (v : VReg) (p offset : Reg) (s : State) (hp : p ≠ .r0)
    (hw : InRegions s.wr (s.gpr p + s.gpr offset) 16) :
    WP isa (.block [.stxvd2x v p offset]) s (· = {s with
      mem := s.mem.write (s.gpr p + s.gpr offset) 16 (swapDwords (s.vpr v))}) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_stxvd2x v p offset s hp hw,
    Option.some.injEq, exists_eq_left']

theorem cipherStates_ok (last : Bool) (k : VReg) (rs : List VReg) (s : State)
    (hn : rs.Nodup) (hk : k ∉ rs) (rk : List Byte)
    (hkey : VG.Proof.Aes.PPC64LE.Crypto.IsKey (s.vpr k) rk) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.cipherRegs false last k rs)) s fun t =>
      (∀ b ∈ rs, aesState (t.vpr b) = VG.Proof.Aes.PPC64LE.Crypto.transform false last rk
        (aesState (s.vpr b))) ∧ VOnly rs s t := by
  refine WP.mono (vector_map (fun b => .vop (.cipher false last b b k)) (vcipher false last)
    k (fun _ _ => rfl) rs s hn hk) fun t ⟨hv, hf⟩ => ⟨?_, hf⟩
  intro b hb
  rw [hv b hb, VG.Proof.Aes.PPC64LE.Crypto.vcipher_transform false last hkey]

def keyReg (i : Nat) : VReg := Impl.AesGcm.PPC64LE.Blocks.roundKeyRegs.getD i .v8

structure EarlyInv (base : State) (nr : Nat) (w : List Byte)
    (input : Nat → Spec.Aes.State) (j : Nat) (s : State) : Prop where
  effects : VOnly (Impl.AesGcm.PPC64LE.Blocks.rs 8) base s
  val : ∀ i < 8, aesState (cipherAt s i) =
    VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) j

theorem early_step (base : State) (nr : Nat) (w : List Byte) (input : Nat → Spec.Aes.State)
    (keys : ∀ j < 9, VG.Proof.Aes.PPC64LE.Crypto.IsKey (base.vpr (keyReg j))
      (Spec.Aes.roundKey w (j+1))) {j : Nat} (hj : j < 9) (s : State)
    (hs : EarlyInv base nr w input j s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.cipherRegs false false (keyReg j)
      (Impl.AesGcm.PPC64LE.Blocks.rs 8))) s (EarlyInv base nr w input (j+1)) := by
  have facts : ∀ j : Fin 9, keyReg j ∉ Impl.AesGcm.PPC64LE.Blocks.rs 8 := by decide
  have hk := facts ⟨j, hj⟩
  have hkey : VG.Proof.Aes.PPC64LE.Crypto.IsKey (s.vpr (keyReg j)) (Spec.Aes.roundKey w (j+1)) := by
    rw [hs.effects.v _ hk]
    exact keys j hj
  refine WP.mono (cipherStates_ok false (keyReg j) _ s (by decide) hk _ hkey) fun t ⟨hv, hf⟩ => ?_
  refine ⟨(hs.effects.trans hf).weaken (by simp), ?_⟩
  intro i hi
  have hm : Impl.AesGcm.PPC64LE.Blocks.reg i ∈ Impl.AesGcm.PPC64LE.Blocks.rs 8 :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  rw [cipherAt, hv _ hm]
  have hsi := hs.val i hi
  rw [cipherAt] at hsi
  rw [hsi]
  exact VG.Proof.Aes.PPC64LE.Crypto.middle_succ false nr w (input i) j

theorem keyRounds_ok (nr : Nat) (w : List Byte) (input : Nat → Spec.Aes.State) (s : State)
    (keys : ∀ j < 9, VG.Proof.Aes.PPC64LE.Crypto.IsKey (s.vpr (keyReg j)) (Spec.Aes.roundKey w (j+1)))
    (hval : ∀ i < 8, aesState (cipherAt s i) =
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 0) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.keyRounds) s (EarlyInv s nr w input 9) := by
  have he : Impl.AesGcm.PPC64LE.Blocks.roundKeyRegs = (List.range 9).map keyReg := by decide
  rw [Impl.AesGcm.PPC64LE.Blocks.keyRounds, he, List.flatMap_map]
  exact wp_range_flatMap (M := isa) (EarlyInv s nr w input)
    (fun j t hj ht => early_step s nr w input keys hj t ht) 9 (Nat.le_refl _) s ⟨VOnly.refl _ _, hval⟩

theorem rawRound_ok (last : Bool) (s : State) (rk : List Byte)
    (h0 : s.gpr .r0 = 0) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16)
    (hk : VG.Proof.Aes.PPC64LE.Crypto.IsKey (swapDwords (s.mem.read (s.gpr .r9) 16)) rk) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.roundRaw 8 last)) s fun t =>
      (∀ i < 8, aesState (cipherAt t i) = VG.Proof.Aes.PPC64LE.Crypto.transform false last rk
        (aesState (cipherAt s i))) ∧ VOnly (.v8 :: Impl.AesGcm.PPC64LE.Blocks.rs 8) s t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.roundRaw, WP.block_append_iff]
  refine WP.mono (rawLoad_ok .v8 .r9 .r0 s (by decide)
    (by simpa only [h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hr)) fun u ⟨hv, hf⟩ => ?_
  have hkey : VG.Proof.Aes.PPC64LE.Crypto.IsKey (u.vpr .v8) rk := by
    rw [hv, h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    exact hk
  refine WP.mono (cipherStates_ok last .v8 (Impl.AesGcm.PPC64LE.Blocks.rs 8) u
    (by decide) (by decide) rk hkey) fun t ⟨hval, ho⟩ => ⟨?_, hf.trans ho⟩
  intro i hi
  have hm : Impl.AesGcm.PPC64LE.Blocks.reg i ∈ Impl.AesGcm.PPC64LE.Blocks.rs 8 :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hne : Impl.AesGcm.PPC64LE.Blocks.reg i ≠ .v8 := by
    have hn : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ≠ .v8 := by decide
    exact hn ⟨i, hi⟩
  simpa only [cipherAt, hf.v _ (by simpa only [List.mem_singleton] using hne)] using hval _ hm

structure RawCfg (base : State) (nr : Nat) (w : List Byte) : Prop where
  zero : base.gpr .r0 = 0
  min : 9 < nr
  max : nr < 15
  reads : ∀ j ≤ nr, InRegions (base.rd ++ base.wr) (base.gpr .r3 + BitVec.ofNat 64 (16*j)) 16
  keys : ∀ j ≤ nr, VG.Proof.Aes.PPC64LE.Crypto.IsKey
    (swapDwords (base.mem.read (base.gpr .r3 + BitVec.ofNat 64 (16*j)) 16)) (Spec.Aes.roundKey w j)

structure RawInv (base : State) (nr : Nat) (w : List Byte)
    (input : Nat → Spec.Aes.State) (j : Nat) (s : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local [.r9, .r10]
    (.v8 :: Impl.AesGcm.PPC64LE.Blocks.rs 8) base s
  ptr : s.gpr .r9 = base.gpr .r3 + BitVec.ofNat 64 (16*(j+1))
  left : s.gpr .r10 = BitVec.ofNat 64 (nr-1-j)
  val : ∀ i < 8, aesState (cipherAt s i) = VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) j

theorem raw_middle_ok {base : State} {nr : Nat} {w : List Byte} {input : Nat → Spec.Aes.State}
    (cfg : RawCfg base nr w) {j : Nat} (hj : j < nr-1) {s : State}
    (h : RawInv base nr w input j s) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.middle 8)) s (RawInv base nr w input (j+1)) := by
  have hz : s.gpr .r0 = 0 := (h.effects.keep.gpr (by decide)).trans cfg.zero
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16 := by
    rw [h.effects.keep.2.1, h.effects.keep.2.2, h.ptr]
    exact cfg.reads _ (by omega)
  have hk : VG.Proof.Aes.PPC64LE.Crypto.IsKey (swapDwords (s.mem.read (s.gpr .r9) 16))
      (Spec.Aes.roundKey w (j+1)) := by
    rw [h.effects.mem, h.ptr]
    exact cfg.keys _ (by omega)
  rw [Impl.AesGcm.PPC64LE.Blocks.middle, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rawRound_ok false s _ hz hr hk) fun u ⟨hv, ho⟩ => ?_
  have hy : ∀ i < 8, aesState (cipherAt u i) =
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) (j+1) := by
    intro i hi
    rw [hv i hi, h.val i hi]
    exact VG.Proof.Aes.PPC64LE.Crypto.middle_succ false nr w (input i) j
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.advance_run false .r10 u (by decide) (by decide)) fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hf := (h.effects.trans (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector ho)).trans
      ((VG.Proof.Aes.PPC64LE.Crypto.Local.write u .r9 (u.gpr .r9+16)).trans
        (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r10 (u.gpr .r10-1)))
    exact hf.weaken (by simp) (by simp [or_left_comm])
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, ho.gpr, h.ptr]
    change base.gpr .r3 + BitVec.ofNat 64 (16*(j+1)) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
    exact congrArg (fun i => base.gpr .r3 + BitVec.ofNat 64 i) (by omega)
  · simp only [RegUpd.gpr_write_self, ho.gpr, h.left]
    change BitVec.ofNat 64 (nr-1-j) - BitVec.ofNat 64 1 = _
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · intro i hi
    simpa only [cipherAt, vpr_write] using hy i hi

theorem rawLoop_ok {base : State} {nr : Nat} {w : List Byte} {input : Nat → Spec.Aes.State}
    (cfg : RawCfg base nr w) {j : Nat} (hj : j < nr-1) {s : State}
    (h : RawInv base nr w input j s) :
    WP isa (.loop (.block (Impl.AesGcm.PPC64LE.Blocks.middle 8)) (.nonzero .d .r10)) s
      (RawInv base nr w input (nr-1)) := by
  let I : Nat → State → Prop := fun m t => ∃ k, m = nr-1-k ∧ k < nr-1 ∧ RawInv base nr w input k t
  have step : ∀ m t, I m t → WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.middle 8)) t fun u =>
      (eval (.nonzero .d .r10) u = some false ∧ RawInv base nr w input (nr-1) u) ∨
      (eval (.nonzero .d .r10) u = some true ∧ ∃ m' < m, I m' u) := by
    rintro m t ⟨k, rfl, hk, ht⟩
    refine WP.mono (raw_middle_ok cfg hk ht) fun u hu => ?_
    have he : eval (.nonzero .d .r10) u = some (BitVec.ofNat 64 (nr-1-(k+1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hu.left]
    by_cases hl : k+1 = nr-1
    · left
      rw [hl, Nat.sub_self] at he
      exact ⟨he.trans (by decide), hl ▸ hu⟩
    · right
      have hne : BitVec.ofNat 64 (nr-1-(k+1)) ≠ 0 := by
        intro hz
        have hzero := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := cfg.max; omega)] at hzero
        have h0 : (0 : BitVec 64).toNat = 0 := rfl
        rw [h0] at hzero
        omega
      exact ⟨he.trans (by simpa using hne), nr-1-(k+1), by omega, k+1, rfl, by omega, hu⟩
  exact WP.loop (M := isa) I step (nr-1-j) s ⟨j, rfl, hj, h⟩

theorem remaining_ok {base : State} {nr : Nat} {w : List Byte} {input : Nat → Spec.Aes.State}
    (cfg : RawCfg base nr w) {j : Nat} (hj : j ≤ nr-1) {s : State}
    (h : RawInv base nr w input j s) :
    WP isa (.ite (.zero .d .r10) (.block [])
      (.loop (.block (Impl.AesGcm.PPC64LE.Blocks.middle 8)) (.nonzero .d .r10))) s
      (RawInv base nr w input (nr-1)) := by
  by_cases heq : j = nr-1
  · have hz : s.gpr .r10 = 0 := by rw [h.left, heq, Nat.sub_self]; rfl
    refine WP.ite true (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]; rfl)
      (fun _ => WP.block_nil (heq ▸ h)) (by simp)
  · have hne : BitVec.ofNat 64 (nr-1-j) ≠ 0 := by
      intro hz
      have hzero := congrArg BitVec.toNat hz
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := cfg.max; omega)] at hzero
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0] at hzero
      omega
    refine WP.ite false (by simpa only [eval, State.read, Size.bits, BitVec.setWidth_eq,
      h.left, Option.some.injEq, beq_eq_false_iff_ne] using hne) (by simp) (fun _ => ?_)
    exact rawLoop_ok cfg (by omega) h

theorem raw_last_ok {base : State} {nr : Nat} {w : List Byte} {input : Nat → Spec.Aes.State}
    (cfg : RawCfg base nr w) {s : State} (h : RawInv base nr w input (nr-1) s) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.roundRaw 8 true)) s fun t =>
      (∀ i < 8, aesState (cipherAt t i) = Spec.Aes.cipher nr w (input i)) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local [.r9, .r10]
        (.v8 :: Impl.AesGcm.PPC64LE.Blocks.rs 8) base t := by
  have hz : s.gpr .r0 = 0 := (h.effects.keep.gpr (by decide)).trans cfg.zero
  have he : nr-1+1 = nr := by have := cfg.min; omega
  have hptr : s.gpr .r9 = base.gpr .r3 + BitVec.ofNat 64 (16*nr) := by
    simpa only [he] using h.ptr
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16 := by
    rw [h.effects.keep.2.1, h.effects.keep.2.2, hptr]
    exact cfg.reads _ (Nat.le_refl _)
  have hk : VG.Proof.Aes.PPC64LE.Crypto.IsKey (swapDwords (s.mem.read (s.gpr .r9) 16))
      (Spec.Aes.roundKey w nr) := by
    rw [h.effects.mem, hptr]
    exact cfg.keys _ (Nat.le_refl _)
  refine WP.mono (rawRound_ok true s _ hz hr hk) fun t ⟨hv, ho⟩ => ⟨?_, ?_⟩
  · intro i hi
    rw [hv i hi, h.val i hi]
    exact VG.Proof.Aes.PPC64LE.Crypto.middle_last false nr w (input i)
  · exact (h.effects.trans (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector ho)).weaken
      (by simp) (by simp [or_left_comm])

theorem packEven_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.packEven) s fun t =>
      t.vpr .v8 = VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair (s.vpr .v12) (s.vpr .v8) ∧
      t.vpr T = VG.Proof.Gcm.PPC64LE.Vpmsum.highPair (s.vpr .v12) (s.vpr .v8) ∧
      VOnly [.v9, T, .v8] s t := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.packEven, runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.Gcm.PPC64LE.Vpmsum.exec_shift8, vpr_writeV, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · exact VG.Proof.Gcm.PPC64LE.Vpmsum.half_swap_right _ _
  · exact VG.Proof.Gcm.PPC64LE.Vpmsum.swap_half_swap_left _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2, ite_false]

structure LoadInv (base : State) (k : Nat) (s : State) : Prop where
  effects : VOnly Impl.AesGcm.PPC64LE.Blocks.dataRegs base s
  val : ∀ i < k, s.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i) =
    swapDwords (base.mem.read (base.gpr .r6 + BitVec.ofNat 64 (16*i)) 16)

theorem dataLoad_step (base : State)
    (offsets : ∀ i < 8, base.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset i) = BitVec.ofNat 64 (16*i))
    (reads : ∀ i < 8, InRegions (base.rd ++ base.wr) (base.gpr .r6+BitVec.ofNat 64 (16*i)) 16)
    {k : Nat} (hk : k < 8) (s : State) (h : LoadInv base k s) :
    WP isa (.block [.lxvd2x (Impl.AesGcm.PPC64LE.Blocks.dataReg k) .r6
      (Impl.AesGcm.PPC64LE.Blocks.dataOffset k)]) s (LoadInv base (k+1)) := by
  have hr : InRegions (s.rd ++ s.wr)
      (s.gpr .r6 + s.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset k)) 16 := by
    rw [h.effects.rd, h.effects.wr, h.effects.gpr, offsets k hk]
    exact reads k hk
  refine WP.mono (rawLoad_ok _ .r6 _ s (by decide) hr) fun t ⟨hv, hf⟩ => ?_
  have mems : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.dataReg i ∈ Impl.AesGcm.PPC64LE.Blocks.dataRegs := by decide
  refine ⟨(h.effects.trans hf).weaken (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact mems ⟨k, hk⟩), ?_⟩
  intro i hi
  by_cases he : i=k
  · subst i
    rw [hv, h.effects.mem, h.effects.gpr, offsets k hk]
  · have hne : Impl.AesGcm.PPC64LE.Blocks.dataReg i ≠ Impl.AesGcm.PPC64LE.Blocks.dataReg k := by
      have inj : ∀ i k : Fin 8, Impl.AesGcm.PPC64LE.Blocks.dataReg i = Impl.AesGcm.PPC64LE.Blocks.dataReg k → i.val=k.val := by decide
      exact fun hbad => he (inj ⟨i, by omega⟩ ⟨k,hk⟩ hbad)
    rw [hf.v _ (by simpa only [List.mem_singleton] using hne)]
    exact h.val i (by omega)

theorem dataLoad_ok (s : State)
    (offsets : ∀ i < 8, s.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset i) = BitVec.ofNat 64 (16*i))
    (reads : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .r6+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.dataLoad) s (LoadInv s 8) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.dataLoad]
  exact wp_range_flatMap (M := isa) (LoadInv s)
    (fun k t hk ht => dataLoad_step s offsets reads hk t ht) 8 (Nat.le_refl _) s
    ⟨VOnly.refl _ _, fun _ hi => by omega⟩

theorem data_separated : ∀ i j : Fin 8,
    Impl.AesGcm.PPC64LE.Blocks.reg i ≠ Impl.AesGcm.PPC64LE.Blocks.dataReg j := by decide

theorem data_injective : ∀ i j : Fin 8,
    Impl.AesGcm.PPC64LE.Blocks.dataReg i = Impl.AesGcm.PPC64LE.Blocks.dataReg j → i.val=j.val := by decide

theorem state_injective : ∀ i j : Fin 8,
    Impl.AesGcm.PPC64LE.Blocks.reg i = Impl.AesGcm.PPC64LE.Blocks.reg j → i.val=j.val := by decide

theorem mixStep_ok (i : Fin 8) (s : State)
    (hm : s.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask) :
    WP isa (.block
      ([.vop (.perm (Impl.AesGcm.PPC64LE.Blocks.dataReg i) (Impl.AesGcm.PPC64LE.Blocks.dataReg i)
          (Impl.AesGcm.PPC64LE.Blocks.dataReg i) .v19),
        .vop (.logic .xor (Impl.AesGcm.PPC64LE.Blocks.reg i) (Impl.AesGcm.PPC64LE.Blocks.reg i)
          (Impl.AesGcm.PPC64LE.Blocks.dataReg i))] : List Instr)) s fun t =>
      t.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i) =
        VG.Proof.Aes.PPC64LE.Crypto.flip (s.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i)) ∧
      t.vpr (Impl.AesGcm.PPC64LE.Blocks.reg i) = s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg i) ^^^
        VG.Proof.Aes.PPC64LE.Crypto.flip (s.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i)) ∧
      VOnly [Impl.AesGcm.PPC64LE.Blocks.dataReg i, Impl.AesGcm.PPC64LE.Blocks.reg i] s t := by
  have hne := data_separated i i
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.Aes.PPC64LE.Crypto.exec_flip _ _ _ hm,
    VG.Proof.Gcm.PPC64LE.Vpmsum.exec_xor, vpr_writeV, hne, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · rw [ite_eq_right (Ne.symm hne)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2, ite_false]

def mixValue (base : State) (i : Nat) : BitVec 128 := cipherAt base i ^^^
  VG.Proof.Aes.PPC64LE.Crypto.flip (base.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i))

def mixRegs : List VReg := Impl.AesGcm.PPC64LE.Blocks.dataRegs ++ Impl.AesGcm.PPC64LE.Blocks.rs 8

structure MixInv (base : State) (k : Nat) (s : State) : Prop where
  effects : VOnly mixRegs base s
  val : ∀ i : Fin 8, s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg i) =
    if i.val < k then mixValue base i else cipherAt base i
  temps : ∀ i : Fin 8, s.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i) =
    if i.val < k then VG.Proof.Aes.PPC64LE.Crypto.flip (base.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i))
    else base.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i)

theorem dataMix_step (base : State) (hm : base.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask)
    {k : Nat} (hk : k < 8) (s : State) (h : MixInv base k s) :
    WP isa (.block
      ([.vop (.perm (Impl.AesGcm.PPC64LE.Blocks.dataReg k) (Impl.AesGcm.PPC64LE.Blocks.dataReg k)
          (Impl.AesGcm.PPC64LE.Blocks.dataReg k) .v19),
        .vop (.logic .xor (Impl.AesGcm.PPC64LE.Blocks.reg k) (Impl.AesGcm.PPC64LE.Blocks.reg k)
          (Impl.AesGcm.PPC64LE.Blocks.dataReg k))] : List Instr)) s (MixInv base (k+1)) := by
  have hm' : s.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask := (h.effects.v .v19 (by decide)).trans hm
  refine WP.mono (mixStep_ok ⟨k,hk⟩ s hm') fun t ⟨ht, hv, hf⟩ => ?_
  have hv0 := h.val ⟨k,hk⟩
  have ht0 := h.temps ⟨k,hk⟩
  simp only [Nat.lt_irrefl, ite_false] at hv0 ht0
  have mems : ∀ i : Fin 8,
      Impl.AesGcm.PPC64LE.Blocks.dataReg i ∈ mixRegs ∧ Impl.AesGcm.PPC64LE.Blocks.reg i ∈ mixRegs := by decide
  refine ⟨(h.effects.trans hf).weaken (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (mems ⟨k,hk⟩).1
      · exact (mems ⟨k,hk⟩).2), ?_, ?_⟩
  · intro i
    by_cases he : i.val=k
    · have hix : i = ⟨k,hk⟩ := Fin.ext he
      subst i
      rw [hv, hv0, ht0, ite_eq_left (show k < k+1 by omega)]
      rfl
    · have hne : Impl.AesGcm.PPC64LE.Blocks.reg i ≠ Impl.AesGcm.PPC64LE.Blocks.reg k :=
        fun heq => he (state_injective i ⟨k,hk⟩ heq)
      have hfree : Impl.AesGcm.PPC64LE.Blocks.reg i ∉
          [Impl.AesGcm.PPC64LE.Blocks.dataReg k, Impl.AesGcm.PPC64LE.Blocks.reg k] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨data_separated i ⟨k,hk⟩, hne⟩
      rw [hf.v _ hfree, h.val i]
      by_cases hi : i.val < k
      · rw [ite_eq_left hi, ite_eq_left (show i.val < k+1 by omega)]
      · rw [ite_eq_right hi, ite_eq_right (show ¬i.val < k+1 by omega)]
  · intro i
    by_cases he : i.val=k
    · have hix : i = ⟨k,hk⟩ := Fin.ext he
      subst i
      rw [ht, ht0, ite_eq_left (show k < k+1 by omega)]
    · have hne : Impl.AesGcm.PPC64LE.Blocks.dataReg i ≠ Impl.AesGcm.PPC64LE.Blocks.dataReg k :=
        fun heq => he (data_injective i ⟨k,hk⟩ heq)
      have hfree : Impl.AesGcm.PPC64LE.Blocks.dataReg i ∉
          [Impl.AesGcm.PPC64LE.Blocks.dataReg k, Impl.AesGcm.PPC64LE.Blocks.reg k] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hne, Ne.symm (data_separated ⟨k,hk⟩ i)⟩
      rw [hf.v _ hfree, h.temps i]
      by_cases hi : i.val < k
      · rw [ite_eq_left hi, ite_eq_left (show i.val < k+1 by omega)]
      · rw [ite_eq_right hi, ite_eq_right (show ¬i.val < k+1 by omega)]

theorem dataMix_ok (s : State) (hm : s.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.dataMix) s (MixInv s 8) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.dataMix]
  exact wp_range_flatMap (M := isa) (MixInv s)
    (fun k t hk ht => dataMix_step s hm hk t ht) 8 (Nat.le_refl _) s
    ⟨VOnly.refl _ _, fun _ => by simp only [cipherAt, Nat.not_lt_zero, ite_false],
      fun _ => by simp only [Nat.not_lt_zero, ite_false]⟩

structure StoreInv (base : State) (m₀ : Mem) (D : Addr) (n k c : Nat)
    (F : Nat → Spec.Aes.State) (s : State) : Prop where
  keep : Keep [] base s
  processed : VG.Proof.Aes.Memory.Processed m₀ s.mem D n (k+c) F
  frame : Frame [⟨D,16*n⟩] base.mem s.mem
  v : ∀ r, r ∉ Impl.AesGcm.PPC64LE.Blocks.dataRegs → s.vpr r = base.vpr r

theorem dataWrite_step {base s : State} {m₀ : Mem} {D : Addr} {n k c : Nat}
    {F : Nat → Spec.Aes.State} (hc : c < 8) (hkn : k+8 ≤ n) (hsize : 16*n ≤ 2^64)
    (hm : base.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask)
    (ptr : base.gpr .r6 = D + BitVec.ofNat 64 (16*k))
    (offsets : ∀ i < 8, base.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset i) = BitVec.ofNat 64 (16*i))
    (writes : ∀ i < 8, InRegions base.wr (D+BitVec.ofNat 64 (16*(k+i))) 16)
    (values : ∀ i < 8, aesState (cipherAt base i) = F (k+i))
    (h : StoreInv base m₀ D n k c F s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.storePerm (Impl.AesGcm.PPC64LE.Blocks.dataReg c)
      (Impl.AesGcm.PPC64LE.Blocks.reg c) .r6 (Impl.AesGcm.PPC64LE.Blocks.dataOffset c))) s
      (StoreInv base m₀ D n k (c+1) F) := by
  have hg : s.gpr = base.gpr := funext fun r => h.keep.gpr (by simp)
  have addr : s.gpr .r6 + s.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset c) =
      D + BitVec.ofNat 64 (16*(k+c)) := by
    rw [hg, offsets c hc, ptr, Offset.add_add]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
  have hw : InRegions s.wr (s.gpr .r6+s.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset c)) 16 := by
    rw [h.keep.2.2, addr]
    exact writes c hc
  have hmask : s.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask := (h.v .v19 (by decide)).trans hm
  have free : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ∉ Impl.AesGcm.PPC64LE.Blocks.dataRegs := by decide
  have hx : aesState (s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg c)) = F (k+c) := by
    rw [h.v _ (free ⟨c,hc⟩)]
    exact values c hc
  have hp := h.processed.store hsize (show k+c < n by omega)
    (v := rev128 (s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg c))) (by
      intro j hj
      change VG.VectorCrypto.vbyte (rev128 (s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg c))) j = _
      rw [← VG.Proof.Aes.Vector.getD_st _ hj]
      exact congrArg (fun x : Spec.Aes.State => x.getD j 0) hx)
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.storePerm_ok _ _ .r6 _ s (by decide) hmask hw)
    fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      simpa only [gpr_writeV] using h.keep.gpr hr
    · simpa only [rd_writeV] using h.keep.2.1
    · simpa only [wr_writeV] using h.keep.2.2
  · change VG.Proof.Aes.Memory.Processed m₀
      (s.mem.write (s.gpr .r6+s.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset c)) 16
        (rev128 (s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg c)))) D n (k+(c+1)) F
    rw [addr]
    simpa only [Nat.add_assoc] using hp.1
  · change Frame [⟨D,16*n⟩] base.mem
      (s.mem.write (s.gpr .r6+s.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset c)) 16
        (rev128 (s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg c))))
    rw [addr]
    exact h.frame.trans hp.2
  · intro r hr
    have mems : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.dataReg i ∈ Impl.AesGcm.PPC64LE.Blocks.dataRegs := by decide
    have hne : r ≠ Impl.AesGcm.PPC64LE.Blocks.dataReg c := fun he => hr (he ▸ mems ⟨c,hc⟩)
    change (s.writeV (Impl.AesGcm.PPC64LE.Blocks.dataReg c)
      (VG.Proof.Aes.PPC64LE.Crypto.flip (s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg c)))).vpr r = _
    rw [vpr_writeV, ite_eq_right hne]
    exact h.v r hr

theorem dataWrite_ok (base : State) (m₀ : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State)
    (hkn : k+8 ≤ n) (hsize : 16*n ≤ 2^64)
    (hm : base.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask)
    (ptr : base.gpr .r6 = D + BitVec.ofNat 64 (16*k))
    (offsets : ∀ i < 8, base.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset i) = BitVec.ofNat 64 (16*i))
    (writes : ∀ i < 8, InRegions base.wr (D+BitVec.ofNat 64 (16*(k+i))) 16)
    (values : ∀ i < 8, aesState (cipherAt base i) = F (k+i))
    (processed : VG.Proof.Aes.Memory.Processed m₀ base.mem D n k F) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.dataWrite) base (StoreInv base m₀ D n k 8 F) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.dataWrite]
  exact wp_range_flatMap (M := isa) (StoreInv base m₀ D n k · F)
    (fun c t hc ht => dataWrite_step hc hkn hsize hm ptr offsets writes values ht)
    8 (Nat.le_refl _) base
    ⟨Keep.refl _ _, by simpa only [Nat.add_zero] using processed, Frame.refl _ _, fun _ _ => rfl⟩

structure CopyKeyResult (s t : State) : Prop where
  keep : Keep [] s t
  v : ∀ r, r ≠ .v8 → t.vpr r = s.vpr r
  value : t.vpr .v8 = rev128 (s.mem.read (s.gpr .r9) 16)
  mem : t.mem = s.mem.write (s.gpr .r11) 16
    (swapDwords (rev128 (s.mem.read (s.gpr .r9) 16)))

structure CacheLoadResult (vec : VReg) (src dst offset : Reg) (s t : State) : Prop where
  keep : Keep [] s t
  v : ∀ r, r ≠ vec → t.vpr r=s.vpr r
  value : t.vpr vec=rev128 (s.mem.read (s.gpr src) 16)
  mem : t.mem=s.mem.write (s.gpr dst+s.gpr offset) 16
    (swapDwords (rev128 (s.mem.read (s.gpr src) 16)))

theorem cacheLoad_ok (v : VReg) (src dst offset : Reg) (s : State)
    (hp : src ≠ .r0) (hq : dst ≠ .r0) (hv : v ≠ .v19)
    (h0 : s.gpr .r0=0) (hm : s.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask)
    (hr : InRegions (s.rd++s.wr) (s.gpr src) 16)
    (hw : InRegions s.wr (s.gpr dst+s.gpr offset) 16) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.cacheLoad v src dst offset)) s (CacheLoadResult v src dst offset s) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.cacheLoad,WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.load_ok v src s hp hv h0 hm hr) fun u ⟨hu,hf⟩ => ?_
  have hw' : InRegions u.wr (u.gpr dst+u.gpr offset) 16 := by
    simpa only [hf.wr,hf.gpr] using hw
  refine WP.mono (rawStore_ok v dst offset u hq hw') fun t ht => ?_
  subst t
  refine ⟨⟨fun r _ => congrFun hf.gpr r,hf.rd,hf.wr⟩,?_,hu,?_⟩
  · intro r hr
    exact hf.v r (by simpa only [List.mem_singleton] using hr)
  · change u.mem.write (u.gpr dst+u.gpr offset) 16 (swapDwords (u.vpr v))=_
    rw [hf.mem,hf.gpr,hu]

theorem copyKey_ok (s : State) (h0 : s.gpr .r0 = 0)
    (hm : s.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16)
    (hw : InRegions s.wr (s.gpr .r11) 16) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.copyKey) s (CopyKeyResult s) := by
  have hw' : InRegions s.wr (s.gpr .r11+s.gpr .r0) 16 := by
    simpa only [h0,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw
  refine WP.mono (cacheLoad_ok .v8 .r9 .r11 .r0 s (by decide) (by decide) (by decide) h0 hm hr hw')
    fun t ht => ⟨ht.keep,ht.v,ht.value,?_⟩
  simpa only [h0,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using ht.mem

/-- Native byte layout used by `lxvd2x` for a cached round key. -/
def cachedKey (base : State) (j : Nat) : BitVec 128 :=
  swapDwords (rev128 (base.mem.read (base.gpr .r9 + BitVec.ofNat 64 (16*j)) 16))

def cachedState (base : State) (j : Nat) : Spec.Aes.State :=
  VG.Proof.Aes.Vector.st (cachedKey base j)

structure CacheCfg (base : State) (count : Nat) : Prop where
  positive : 0 < count
  bound : count ≤ 15
  zero : base.gpr .r0 = 0
  mask : base.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask
  left : base.gpr .r12 = BitVec.ofNat 64 count
  reads : ∀ j < count, InRegions (base.rd ++ base.wr)
    (base.gpr .r9 + BitVec.ofNat 64 (16*j)) 16
  writes : ∀ j < count, InRegions base.wr
    (base.gpr .r11 + BitVec.ofNat 64 (16*j)) 16
  disjoint : (⟨base.gpr .r9,16*count⟩ : Region).Disjoint ⟨base.gpr .r11,16*count⟩

structure CacheInv (base : State) (count j : Nat) (s : State) : Prop where
  keep : Keep [.r9,.r11,.r12] base s
  v : ∀ r, r ≠ .v8 → s.vpr r = base.vpr r
  src : s.gpr .r9 = base.gpr .r9 + BitVec.ofNat 64 (16*j)
  dst : s.gpr .r11 = base.gpr .r11 + BitVec.ofNat 64 (16*j)
  left : s.gpr .r12 = BitVec.ofNat 64 (count-j)
  processed : VG.Proof.Aes.Memory.Processed base.mem s.mem (base.gpr .r11) count j (cachedState base)
  frame : Frame [⟨base.gpr .r11,16*count⟩] base.mem s.mem

theorem cacheAdvance_ok (s : State) :
    WP isa (.block ([.addi .r9 .r9 16, .addi .r11 .r11 16, .subi .r12 .r12 1] : List Instr)) s
      (· = ((s.write .r9 (s.gpr .r9+16)).write .r11 (s.gpr .r11+16)).write .r12 (s.gpr .r12-1)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (n := .r9) (imm := 16) (by decide) (by decide),
    exec_addi (n := .r11) (imm := 16) (by decide) (by decide),
    exec_subi (n := .r12) (imm := 1) (by decide) (by decide), RegUpd.gpr_write, reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  rfl

theorem cacheStep_ok {base : State} {count j : Nat} (cfg : CacheCfg base count)
    (hj : j < count) {s : State} (h : CacheInv base count j s) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.cacheStep) s (CacheInv base count (j+1)) := by
  have hz : s.gpr .r0 = 0 := (h.keep.gpr (by decide)).trans cfg.zero
  have hm : s.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask := (h.v _ (by decide)).trans cfg.mask
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16 := by
    rw [h.keep.2.1, h.keep.2.2, h.src]
    exact cfg.reads j hj
  have hw : InRegions s.wr (s.gpr .r11) 16 := by
    rw [h.keep.2.2, h.dst]
    exact cfg.writes j hj
  have hs : s.mem.read (s.gpr .r9) 16 =
      base.mem.read (base.gpr .r9 + BitVec.ofNat 64 (16*j)) 16 := by
    rw [h.src]
    exact h.frame.read (Offset.contains_base _ (d := 16*j) (n := 16) (k := 16*count)
      (by omega) (by have := cfg.bound; omega))
      (by simpa only [List.mem_singleton, forall_eq] using cfg.disjoint) (by decide)
  rw [Impl.AesGcm.PPC64LE.Blocks.cacheStep, WP.block_append_iff]
  refine WP.mono (copyKey_ok s hz hm hr hw) fun u hu => ?_
  have hprocessed := h.processed.store (by have := cfg.bound; omega) hj
    (v := cachedKey base j) (fun i hi => (VG.Proof.Aes.Vector.getD_st _ hi).symm)
  have hmem : u.mem = s.mem.write (base.gpr .r11+BitVec.ofNat 64 (16*j)) 16 (cachedKey base j) := by
    rw [hu.mem, h.dst, hs]
    rfl
  refine WP.mono (cacheAdvance_ok u) fun t ht => ?_
  subst t
  have hg : u.gpr = s.gpr := funext fun r => hu.keep.gpr (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hlocal := ((VG.Proof.Aes.PPC64LE.Crypto.Local.write u .r9 (u.gpr .r9+16)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r11 (u.gpr .r11+16))).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r12 (u.gpr .r12-1))
    exact ((h.keep.trans hu.keep).trans hlocal.keep).mono (by simp)
  · intro r hr
    simpa only [vpr_write] using (hu.v r hr).trans (h.v r hr)
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, hg, h.src]
    change base.gpr .r9 + BitVec.ofNat 64 (16*j) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
    exact congrArg (fun i => base.gpr .r9+BitVec.ofNat 64 i) (by omega)
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, hg, h.dst]
    change base.gpr .r11 + BitVec.ofNat 64 (16*j) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
    exact congrArg (fun i => base.gpr .r11+BitVec.ofNat 64 i) (by omega)
  · simp only [RegUpd.gpr_write_self, hg, h.left]
    change BitVec.ofNat 64 (count-j) - BitVec.ofNat 64 1 = _
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · simpa only [RegUpd.mem_write, hmem] using hprocessed.1
  · simpa only [RegUpd.mem_write, hmem] using h.frame.trans hprocessed.2


theorem cacheLoop_ok {base : State} {count j : Nat} (cfg : CacheCfg base count)
    (hj : j < count) {s : State} (h : CacheInv base count j s) :
    WP isa (.loop (.block Impl.AesGcm.PPC64LE.Blocks.cacheStep) (.nonzero .d .r12)) s
      (CacheInv base count count) := by
  let I : Nat → State → Prop := fun m t => ∃ k, m=count-k ∧ k<count ∧ CacheInv base count k t
  have step : ∀ m t, I m t → WP isa (.block Impl.AesGcm.PPC64LE.Blocks.cacheStep) t fun u =>
      (eval (.nonzero .d .r12) u = some false ∧ CacheInv base count count u) ∨
      (eval (.nonzero .d .r12) u = some true ∧ ∃ m' < m, I m' u) := by
    rintro m t ⟨k, rfl, hk, ht⟩
    refine WP.mono (cacheStep_ok cfg hk ht) fun u hu => ?_
    have he : eval (.nonzero .d .r12) u = some (BitVec.ofNat 64 (count-(k+1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hu.left]
    by_cases hl : k+1=count
    · left
      rw [hl, Nat.sub_self] at he
      exact ⟨he.trans (by decide), hl ▸ hu⟩
    · right
      have hne : BitVec.ofNat 64 (count-(k+1)) ≠ 0 := by
        intro hz
        have hzero := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := cfg.bound; omega)] at hzero
        have h0 : (0 : BitVec 64).toNat=0 := rfl
        rw [h0] at hzero
        omega
      exact ⟨he.trans (by simpa using hne), count-(k+1), by omega, k+1, rfl, by omega, hu⟩
  exact WP.loop (M := isa) I step (count-j) s ⟨j,rfl,hj,h⟩

theorem cacheKeys_ok (base : State) (count : Nat) (cfg : CacheCfg base count) :
    WP isa (.loop (.block Impl.AesGcm.PPC64LE.Blocks.cacheStep) (.nonzero .d .r12)) base
      (CacheInv base count count) := by
  exact cacheLoop_ok cfg cfg.positive ⟨Keep.refl _ _, fun _ _ => rfl,
    by simp only [Nat.mul_zero, BitVec.add_zero],
    by simp only [Nat.mul_zero, BitVec.add_zero],
    by simpa only [Nat.sub_zero] using cfg.left,
    VG.Proof.Aes.Memory.Processed.refl _ _ _ _, Frame.refl _ _⟩

theorem cachedKey_read {base s : State} {count j : Nat} (h : CacheInv base count count s)
    (hj : j < count) :
    s.mem.read (base.gpr .r11 + BitVec.ofNat 64 (16*j)) 16 = cachedKey base j := by
  have hs := h.processed.stateAt hj (Nat.le_refl _)
  apply Mem.read_eq_of_bytes
  intro i hi
  have hx := congrArg (fun x : Spec.Aes.State => x.getD i 0) hs
  rw [cachedState, VG.Proof.Aes.Vector.getD_st _ hi, Spec.Aes.stateAt,
    VG.Proof.Aes.Vector.getD_ofFn hi] at hx
  exact hx


def finishRegs : Fin 6 → VReg
  | ⟨0,_⟩ => LO | ⟨1,_⟩ => MID | ⟨2,_⟩ => HI
  | ⟨3,_⟩ => T | ⟨4,_⟩ => U | _ => .v13

theorem ghFinish_ok (s : State) (hc : s.vpr .v13 = poly ++ poly) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.ghFinish) s fun t =>
      t.vpr .v10 = VG.Proof.Gcm.Clmul.ext8 (VG.Proof.Gcm.Clmul.reduce (product s))
        (VG.Proof.Gcm.Clmul.reduce (product s)) ∧ VOnly [U,LO,MID,HI,T,.v10] s t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.ghFinish, WP.block_append_iff, WP.block_append_iff]
  have hz : WP isa (.block ([.vop (.logic .xor U U U)] : List Instr)) s
      (· = s.writeV U 0) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      VG.Proof.Gcm.PPC64LE.Vpmsum.exec_xor, BitVec.xor_self, Option.some.injEq, exists_eq_left']
    rfl
  refine WP.mono hz fun u hu => ?_
  subst u
  have hpoly : (s.writeV U 0).vpr .v13 = poly ++ poly := by
    simpa only [vpr_writeV, reduceCtorEq, ite_false] using hc
  have hzero : (s.writeV U 0).vpr U = 0 := by simp only [vpr_writeV, ite_true]
  refine WP.mono (reduceWith_ok finishRegs
    (show ∀ i j : Fin 6, finishRegs i=finishRegs j → i=j from by decide) .v10 _ hpoly hzero)
    fun u ⟨hv,ho⟩ => ?_
  change u.vpr .v10 = VG.Proof.Gcm.Clmul.reduce
    ⟨(s.writeV U 0).vpr LO,(s.writeV U 0).vpr MID,(s.writeV U 0).vpr HI⟩ at hv
  change VOnly [LO,MID,HI,T,.v10] (s.writeV U 0) u at ho
  have hp : u.vpr .v10 = VG.Proof.Gcm.Clmul.reduce (product s) := by
    simpa only [vpr_writeV, reduceCtorEq, ite_false, product] using hv
  refine WP.mono (vector_step (.vop (.sldoi .v10 .v10 .v10 8)) .v10 _ u
    (VG.Proof.Gcm.PPC64LE.Vpmsum.exec_shift8 .v10 .v10 .v10 u)) fun t ⟨ht,hf⟩ => ?_
  refine ⟨?_, ?_⟩
  · rw [ht, VG.Proof.Gcm.PPC64LE.Vpmsum.half_self, hp]
  · have hs : VOnly [U] s (s.writeV U 0) :=
      ⟨fun r hr => by
        rw [vpr_writeV, ite_eq_right (by simpa only [List.mem_singleton] using hr)],
       gpr_writeV .., mem_writeV .., rd_writeV .., wr_writeV .., sp_writeV .., lr_writeV ..⟩
    exact (hs.trans (ho.trans hf)).weaken (by simp [or_left_comm])


def ghSaved (j : Nat) (s : State) : VG.Proof.Gcm.Clmul.Prod :=
  if j=0 then VG.Proof.Gcm.Clmul.Prod.zero
  else if j=4 then product s else ⟨s.vpr .v10,s.vpr .v11,s.vpr .v12⟩

theorem exec_copyVector (d n : VReg) (s : State) :
    exec (.vop (.logic .or d n n)) s = some (s.writeV d (s.vpr n)) := by
  change some (s.writeV d (s.vpr n ||| s.vpr n)) = _
  rw [BitVec.or_self]

theorem ghAcc_first (s : State) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.ghAcc 0)) s fun t =>
      ghSaved 1 t = product s ∧ VOnly [.v10,.v11,.v12] s t := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.ghAcc, ite_true, runBlock_cons, runStep_some, runBlock_nil,
    exec_copyVector, vpr_writeV, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨?_, gpr_writeV .., mem_writeV .., rd_writeV .., wr_writeV .., sp_writeV .., lr_writeV ..⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2, ite_false]

theorem ghAcc_middle (j : Nat) (s : State) (hj : j ≠ 0) (hl : j ≠ 3) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.ghAcc j)) s fun t =>
      (⟨t.vpr .v10,t.vpr .v11,t.vpr .v12⟩ : VG.Proof.Gcm.Clmul.Prod) =
        VG.Proof.Gcm.PPC64LE.Vpmsum.addProd ⟨s.vpr .v10,s.vpr .v11,s.vpr .v12⟩ (product s) ∧
      VOnly [.v10,.v11,.v12] s t := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.ghAcc, hj, hl, ite_false,
    runBlock_cons, runStep_some, runBlock_nil, VG.Proof.Gcm.PPC64LE.Vpmsum.exec_xor,
    vpr_writeV, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨?_, gpr_writeV .., mem_writeV .., rd_writeV .., wr_writeV .., sp_writeV .., lr_writeV ..⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2, ite_false]

theorem ghAcc_last (s : State) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.ghAcc 3)) s fun t =>
      product t = VG.Proof.Gcm.PPC64LE.Vpmsum.addProd
        ⟨s.vpr .v10,s.vpr .v11,s.vpr .v12⟩ (product s) ∧ VOnly [LO,MID,HI] s t := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.ghAcc, ite_false, ite_true,
    runBlock_cons, runStep_some, runBlock_nil, VG.Proof.Gcm.PPC64LE.Vpmsum.exec_xor,
    vpr_writeV, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, gpr_writeV .., mem_writeV .., rd_writeV .., wr_writeV .., sp_writeV .., lr_writeV ..⟩⟩
  · simp only [product, VG.Proof.Gcm.PPC64LE.Vpmsum.addProd, vpr_writeV,
      reduceCtorEq, ite_false, ite_true, BitVec.xor_comm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2, ite_false]


theorem ghAcc_ok (j : Fin 4) (s : State) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.ghAcc j)) s fun t =>
      ghSaved (j+1) t = VG.Proof.Gcm.PPC64LE.Vpmsum.addProd (ghSaved j s) (product s) ∧
      VOnly [.v10,.v11,.v12,LO,MID,HI] s t := by
  by_cases hz : j.val=0
  · simp only [hz]
    refine WP.mono (ghAcc_first s) fun t ⟨hv,hf⟩ => ⟨?_, hf.weaken (by simp)⟩
    simpa [ghSaved, VG.Proof.Gcm.Clmul.Prod.zero,
      VG.Proof.Gcm.PPC64LE.Vpmsum.addProd, product] using hv
  · by_cases hl : j.val=3
    · simp only [hl]
      refine WP.mono (ghAcc_last s) fun t ⟨hv,hf⟩ => ⟨?_, hf.weaken (by simp)⟩
      simpa [ghSaved] using hv
    · refine WP.mono (ghAcc_middle j s hz hl) fun t ⟨hv,hf⟩ => ⟨?_,hf.weaken (by simp)⟩
      simpa only [ghSaved, hz, show j.val ≠ 4 by omega, show j.val+1 ≠ 0 by omega,
        show j.val+1 ≠ 4 by omega, ite_false] using hv


structure GhReadResult (s t : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local [.r21,.r22] [.v8,.v9] s t
  lo : t.vpr .v8 = swapDwords (s.mem.read (s.gpr .r16+s.gpr .r21) 16)
  hi : t.vpr .v9 = swapDwords (s.mem.read (s.gpr .r16+s.gpr .r22) 16)
  first : t.gpr .r21 = s.gpr .r21+32
  second : t.gpr .r22 = s.gpr .r22+32

theorem ghRead_advance (s : State) :
    WP isa (.block ([.addi .r21 .r21 32, .addi .r22 .r22 32] : List Instr)) s
      (· = (s.write .r21 (s.gpr .r21+32)).write .r22 (s.gpr .r22+32)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_addi (n := .r21) (imm := 32) (by decide) (by decide),
    exec_addi (n := .r22) (imm := 32) (by decide) (by decide),
    RegUpd.gpr_write, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  rfl

theorem ghRead_ok (s : State)
    (hrl : InRegions (s.rd++s.wr) (s.gpr .r16+s.gpr .r21) 16)
    (hrh : InRegions (s.rd++s.wr) (s.gpr .r16+s.gpr .r22) 16) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.ghRead) s (GhReadResult s) := by
  have hc : Impl.AesGcm.PPC64LE.Blocks.ghRead =
      ([.lxvd2x .v8 .r16 .r21] : List Instr) ++ [.lxvd2x .v9 .r16 .r22] ++
        [.addi .r21 .r21 32,.addi .r22 .r22 32] := rfl
  rw [hc, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rawLoad_ok .v8 .r16 .r21 s (by decide) hrl) fun u ⟨hl,hf⟩ => ?_
  have hrh' : InRegions (u.rd++u.wr) (u.gpr .r16+u.gpr .r22) 16 := by
    simpa only [hf.rd,hf.wr,hf.gpr] using hrh
  refine WP.mono (rawLoad_ok .v9 .r16 .r22 u (by decide) hrh') fun v ⟨hh,hg⟩ => ?_
  refine WP.mono (ghRead_advance v) fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have he := ((VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hf).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hg)).trans
      ((VG.Proof.Aes.PPC64LE.Crypto.Local.write v .r21 (v.gpr .r21+32)).trans
        (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r22 (v.gpr .r22+32)))
    exact he.weaken (by simp) (by simp)
  · simpa only [vpr_write, hg.v .v8 (by decide)] using hl
  · simpa only [vpr_write, hf.mem, hf.gpr] using hh
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, hg.gpr,hf.gpr]
  · simp only [RegUpd.gpr_write_self,hg.gpr,hf.gpr]


structure GhInjectResult (j : Nat) (s t : State) : Prop where
  effects : VOnly [.v0] s t
  a : cipherAt t (2*j) = if j=0 then cipherAt s (2*j) ^^^ s.vpr .v10 else cipherAt s (2*j)
  b : cipherAt t (2*j+1) = cipherAt s (2*j+1)
  saved : ghSaved j t = ghSaved j s

theorem ghInject_ok (j : Fin 4) (s : State) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.ghInject j)) s (GhInjectResult j s) := by
  by_cases hz : j.val=0
  · rw [Impl.AesGcm.PPC64LE.Blocks.ghInject, ite_eq_left hz]
    refine WP.mono (vector_step (.vop (.logic .xor .v0 .v0 .v10)) .v0 _ s
      (VG.Proof.Gcm.PPC64LE.Vpmsum.exec_xor .v0 .v0 .v10 s)) fun t ⟨hv,hf⟩ => ?_
    refine ⟨hf, ?_, ?_, ?_⟩
    · simp only [hz, Nat.mul_zero, ite_true]
      exact hv
    · simp only [hz, Nat.mul_zero, Nat.zero_add]
      exact hf.v .v1 (by decide)
    · simp only [ghSaved,hz,ite_true]
  · rw [Impl.AesGcm.PPC64LE.Blocks.ghInject, ite_eq_right hz]
    exact WP.block_nil ⟨VOnly.refl _ _, by rw [ite_eq_right hz], rfl, rfl⟩


structure GhPairResult (j : Nat) (h : BitVec 128) (s t : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local [.r21,.r22]
    [.v0,.v8,.v9,U,T,LO,MID,HI,.v10,.v11,.v12] s t
  value : ghSaved (j+1) t = VG.Proof.Gcm.PPC64LE.Vpmsum.addProd (ghSaved j s)
    (VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm h (s.vpr .v10) (cipherAt s) j)
  first : t.gpr .r21=s.gpr .r21+32
  second : t.gpr .r22=s.gpr .r22+32

theorem ghPair_ok (j : Fin 4) (h : BitVec 128) (s : State)
    (hrl : InRegions (s.rd++s.wr) (s.gpr .r16+s.gpr .r21) 16)
    (hrh : InRegions (s.rd++s.wr) (s.gpr .r16+s.gpr .r22) 16)
    (hlo : swapDwords (s.mem.read (s.gpr .r16+s.gpr .r21) 16) =
      VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (7-2*j))
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (6-2*j)))
    (hhi : swapDwords (s.mem.read (s.gpr .r16+s.gpr .r22) 16) =
      VG.Proof.Gcm.PPC64LE.Vpmsum.highPair
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (7-2*j))
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (6-2*j))) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.ghPair j)) s (GhPairResult j h s) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.ghPair, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ghInject_ok j s) fun u hu => ?_
  have hrl' : InRegions (u.rd++u.wr) (u.gpr .r16+u.gpr .r21) 16 := by
    simpa only [hu.effects.rd,hu.effects.wr,hu.effects.gpr] using hrl
  have hrh' : InRegions (u.rd++u.wr) (u.gpr .r16+u.gpr .r22) 16 := by
    simpa only [hu.effects.rd,hu.effects.wr,hu.effects.gpr] using hrh
  refine WP.mono (ghRead_ok u hrl' hrh') fun v hv => ?_
  have hlow := hv.lo.trans (by
    simpa only [hu.effects.mem,hu.effects.gpr] using hlo)
  have hhigh := hv.hi.trans (by
    simpa only [hu.effects.mem,hu.effects.gpr] using hhi)
  refine WP.mono (paired_ok j _ _ v hlow hhigh) fun w ⟨hw,hf⟩ => ?_
  have freeA : ∀ k : Fin 4, Impl.AesGcm.PPC64LE.Blocks.reg (2*k.val) ∉ [.v8,.v9] := by decide
  have freeB : ∀ k : Fin 4, Impl.AesGcm.PPC64LE.Blocks.reg (2*k.val+1) ∉ [.v8,.v9] := by decide
  have ha : cipherAt v (2*j)=cipherAt u (2*j) := hv.effects.v _ (freeA j)
  have hb : cipherAt v (2*j+1)=cipherAt u (2*j+1) := hv.effects.v _ (freeB j)
  have hterm : product w = VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm h (s.vpr .v10) (cipherAt s) j := by
    simpa only [VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm,hashAt,ha,hb,hu.a,hu.b] using hw
  have hsave : ghSaved j w=ghSaved j s := by
    by_cases hz : j.val=0
    · simp only [ghSaved,hz,ite_true]
    · simp only [ghSaved,hz,show j.val ≠ 4 by omega,ite_false]
      simp only [hf.v .v10 (by decide),hf.v .v11 (by decide),hf.v .v12 (by decide),
        hv.effects.v .v10 (by decide),hv.effects.v .v11 (by decide),hv.effects.v .v12 (by decide),
        hu.effects.v .v10 (by decide),hu.effects.v .v11 (by decide),hu.effects.v .v12 (by decide)]
  refine WP.mono (ghAcc_ok j w) fun t ⟨ht,hg⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he := (((VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hu.effects).trans hv.effects).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hf)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hg)
    exact he.weaken (by simp) (by simp [or_left_comm])
  · rw [ht,hsave,hterm]
  · simp only [hg.gpr,hf.gpr,hv.first,hu.effects.gpr]
  · simp only [hg.gpr,hf.gpr,hv.second,hu.effects.gpr]


def ghClobbers : List VReg := [.v0,.v8,.v9,U,T,LO,MID,HI,.v10,.v11,.v12]

def ghSlot (s : State) (r : Reg) (j : Nat) : Addr :=
  s.gpr .r16+(s.gpr r+BitVec.ofNat 64 (32*j))

structure GhFoldCfg (base : State) (h : BitVec 128) : Prop where
  reads : ∀ j < 4, InRegions (base.rd++base.wr) (ghSlot base .r21 j) 16 ∧
    InRegions (base.rd++base.wr) (ghSlot base .r22 j) 16
  lo : ∀ j < 4, swapDwords (base.mem.read (ghSlot base .r21 j) 16) =
    VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair
      (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (7-2*j))
      (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (6-2*j))
  hi : ∀ j < 4, swapDwords (base.mem.read (ghSlot base .r22 j) 16) =
    VG.Proof.Gcm.PPC64LE.Vpmsum.highPair
      (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (7-2*j))
      (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (6-2*j))

def ghPrefix (base : State) (h : BitVec 128) (j : Nat) : VG.Proof.Gcm.Clmul.Prod :=
  (List.range j).foldl (fun p k => VG.Proof.Gcm.PPC64LE.Vpmsum.addProd p
    (VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm h (base.vpr .v10) (cipherAt base) k))
      VG.Proof.Gcm.Clmul.Prod.zero

structure GhFoldInv (base : State) (h : BitVec 128) (j : Nat) (s : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local [.r21,.r22] ghClobbers base s
  first : s.gpr .r21=base.gpr .r21+BitVec.ofNat 64 (32*j)
  second : s.gpr .r22=base.gpr .r22+BitVec.ofNat 64 (32*j)
  value : ghSaved j s=ghPrefix base h j
  start : j=0 → s.vpr .v0=base.vpr .v0 ∧ s.vpr .v10=base.vpr .v10

theorem ghPrefix_succ (base : State) (h : BitVec 128) (j : Nat) :
    ghPrefix base h (j+1)=VG.Proof.Gcm.PPC64LE.Vpmsum.addProd (ghPrefix base h j)
      (VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm h (base.vpr .v10) (cipherAt base) j) := by
  simp only [ghPrefix,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem ghFold_step {base : State} {h : BitVec 128} (cfg : GhFoldCfg base h)
    {j : Nat} (hj : j < 4) {s : State} (hs : GhFoldInv base h j s) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.ghPair j)) s (GhFoldInv base h (j+1)) := by
  have ha : s.gpr .r16+s.gpr .r21=ghSlot base .r21 j := by
    rw [hs.effects.keep.gpr (by decide),hs.first]; rfl
  have hb : s.gpr .r16+s.gpr .r22=ghSlot base .r22 j := by
    rw [hs.effects.keep.gpr (by decide),hs.second]; rfl
  have hrl : InRegions (s.rd++s.wr) (s.gpr .r16+s.gpr .r21) 16 := by
    rw [hs.effects.keep.2.1,hs.effects.keep.2.2,ha]; exact (cfg.reads j hj).1
  have hrh : InRegions (s.rd++s.wr) (s.gpr .r16+s.gpr .r22) 16 := by
    rw [hs.effects.keep.2.1,hs.effects.keep.2.2,hb]; exact (cfg.reads j hj).2
  have hlo := cfg.lo j hj
  have hhi := cfg.hi j hj
  rw [← ha,← hs.effects.mem] at hlo
  rw [← hb,← hs.effects.mem] at hhi
  refine WP.mono (ghPair_ok ⟨j,hj⟩ h s hrl hrh hlo hhi) fun t ht => ?_
  have hterm : VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm h (s.vpr .v10) (cipherAt s) j =
      VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm h (base.vpr .v10) (cipherAt base) j := by
    by_cases hz : j=0
    · have hzv := hs.start hz
      simp only [VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm,hz,Nat.mul_zero,Nat.zero_add,
        ite_true,cipherAt,hzv.2]
      change VG.Proof.Gcm.PPC64LE.Vpmsum.pairedProd
        (VG.Proof.Gcm.Clmul.ext8 (s.vpr .v0 ^^^ base.vpr .v10) (s.vpr .v0 ^^^ base.vpr .v10))
        (VG.Proof.Gcm.Clmul.ext8 (s.vpr .v1) (s.vpr .v1)) _ _ = _
      rw [hzv.1,hs.effects.v .v1 (by decide)]
      rfl
    · have freeA : ∀ k : Fin 4, k.val ≠ 0 → Impl.AesGcm.PPC64LE.Blocks.reg (2*k.val) ∉ ghClobbers := by decide
      have freeB : ∀ k : Fin 4, Impl.AesGcm.PPC64LE.Blocks.reg (2*k.val+1) ∉ ghClobbers := by decide
      simp only [VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalTerm,hz,ite_false,cipherAt,
        hs.effects.v _ (freeA ⟨j,hj⟩ hz),hs.effects.v _ (freeB ⟨j,hj⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hs.effects.trans ht.effects).weaken (by simp) (by simp [ghClobbers])
  · rw [ht.first,hs.first]
    change base.gpr .r21+BitVec.ofNat 64 (32*j)+BitVec.ofNat 64 32 = _
    rw [Offset.add_add]
    exact congrArg (fun i => base.gpr .r21+BitVec.ofNat 64 i) (by omega)
  · rw [ht.second,hs.second]
    change base.gpr .r22+BitVec.ofNat 64 (32*j)+BitVec.ofNat 64 32 = _
    rw [Offset.add_add]
    exact congrArg (fun i => base.gpr .r22+BitVec.ofNat 64 i) (by omega)
  · rw [ht.value,hs.value,hterm,ghPrefix_succ]
  · intro hz; omega

theorem ghPairs_ok (base : State) (h : BitVec 128) (cfg : GhFoldCfg base h) :
    WP isa (.block ((List.range 4).flatMap Impl.AesGcm.PPC64LE.Blocks.ghPair)) base
      (GhFoldInv base h 4) := by
  exact wp_range_flatMap (M := isa) (GhFoldInv base h)
    (fun j t hj ht => ghFold_step cfg hj ht) 4 (Nat.le_refl _) base
    ⟨VG.Proof.Aes.PPC64LE.Crypto.Local.refl _ _ _,
      by simp only [Nat.mul_zero,BitVec.add_zero],
      by simp only [Nat.mul_zero,BitVec.add_zero],rfl,fun _ => ⟨rfl,rfl⟩⟩

theorem ghFold_ok (base : State) (h : BitVec 128) (cfg : GhFoldCfg base h)
    (hc : base.vpr .v13=poly++poly) :
    WP isa (.block ((List.range 4).flatMap Impl.AesGcm.PPC64LE.Blocks.ghPair ++
      Impl.AesGcm.PPC64LE.Blocks.ghFinish)) base fun t =>
      t.vpr .v10=VG.Proof.Gcm.PPC64LE.Vpmsum.canonicalFold h (base.vpr .v10) (cipherAt base) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local [.r21,.r22] ghClobbers base t := by
  rw [WP.block_append_iff]
  refine WP.mono (ghPairs_ok base h cfg) fun s hs => ?_
  have hp : product s=VG.Proof.Gcm.PPC64LE.Vpmsum.foldedProducts h (base.vpr .v10) (cipherAt base) := by
    simpa [ghSaved,ghPrefix,VG.Proof.Gcm.PPC64LE.Vpmsum.foldedProducts] using hs.value
  have hc' : s.vpr .v13=poly++poly := (hs.effects.v .v13 (by decide)).trans hc
  refine WP.mono (ghFinish_ok s hc') fun t ⟨ht,hf⟩ => ⟨?_, ?_⟩
  · rw [ht,hp]; rfl
  · exact (hs.effects.trans (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hf)).weaken
      (by simp) (by simp [ghClobbers,or_left_comm])


theorem ghFold_ghash [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (base : State) (h : BitVec 128)
    (cfg : GhFoldCfg base (VG.Proof.Gcm.PPC64LE.Vpmsum.adjustedKey h))
    (hc : base.vpr .v13=poly++poly) :
    WP isa (.block ((List.range 4).flatMap Impl.AesGcm.PPC64LE.Blocks.ghPair ++
      Impl.AesGcm.PPC64LE.Blocks.ghFinish)) base fun t =>
      t.vpr .v10=Spec.Gcm.ghashFrom h (base.vpr .v10) ((List.range 8).map (cipherAt base)) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local [.r21,.r22] ghClobbers base t := by
  refine WP.mono (ghFold_ok base _ cfg hc) fun t ⟨ht,hf⟩ => ⟨?_,hf⟩
  exact ht.trans (VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw.correct h (base.vpr .v10) (cipherAt base))

theorem counter_advance (cb : Spec.Gcm.Block) (n d : Nat) :
    (Nat.repeat Spec.Gcm.inc32 n cb).extractLsb' 32 96 ++
      ((Nat.repeat Spec.Gcm.inc32 n cb).extractLsb' 0 32+BitVec.ofNat 32 d) =
        Nat.repeat Spec.Gcm.inc32 (n+d) cb := by
  rw [VG.Proof.Aes.repeat_inc32_hi,VG.Proof.Aes.repeat_inc32_lo,counterValue]
  rw [BitVec.ofNat_add,BitVec.add_assoc]

theorem counter_step_ok (i : Fin 6) (s : State) (cb : Spec.Gcm.Block)
    (ht : s.vpr T=0#96++2#32)
    (hv : cipherAt s i=Nat.repeat Spec.Gcm.inc32 i cb) :
    WP isa (.block ([.vop (.add false (Impl.AesGcm.PPC64LE.Blocks.reg (i+2))
      (Impl.AesGcm.PPC64LE.Blocks.reg i) T)] : List Instr)) s fun t =>
      cipherAt t (i+2)=Nat.repeat Spec.Gcm.inc32 (i+2) cb ∧
      VOnly [Impl.AesGcm.PPC64LE.Blocks.reg (i+2)] s t := by
  refine WP.mono (vector_step (.vop (.add false (Impl.AesGcm.PPC64LE.Blocks.reg (i+2))
    (Impl.AesGcm.PPC64LE.Blocks.reg i) T)) _ _ s
      (exec_add_counter _ _ T 2 s ht)) fun t ⟨hval,hf⟩ => ⟨?_,hf⟩
  change cipherAt t (i+2)=_ at hval
  rw [hval,← counter_advance cb i 2]
  rw [← hv]
  rfl

structure CounterStepsInv (base : State) (cb : Spec.Gcm.Block) (j : Nat) (s : State) : Prop where
  effects : VOnly (Impl.AesGcm.PPC64LE.Blocks.rs 8) base s
  value : ∀ i < j+2, cipherAt s i=Nat.repeat Spec.Gcm.inc32 i cb

theorem counterSteps_step {base : State} {cb : Spec.Gcm.Block}
    (ht : base.vpr T=0#96++2#32) {j : Nat} (hj : j<6) {s : State}
    (hs : CounterStepsInv base cb j s) :
    WP isa (.block ([.vop (.add false (Impl.AesGcm.PPC64LE.Blocks.reg (j+2))
      (Impl.AesGcm.PPC64LE.Blocks.reg j) T)] : List Instr)) s (CounterStepsInv base cb (j+1)) := by
  have ht' : s.vpr T=0#96++2#32 := (hs.effects.v T (by decide)).trans ht
  refine WP.mono (counter_step_ok ⟨j,hj⟩ s cb ht' (hs.value j (by omega))) fun t ⟨hv,hf⟩ => ?_
  refine ⟨?_, ?_⟩
  · exact (hs.effects.trans hf).weaken (by
      intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact h
      · rw [List.mem_singleton] at h
        subst r
        exact List.mem_map.mpr ⟨j+2,List.mem_range.mpr (by omega),rfl⟩)
  · intro i hi
    by_cases he : i=j+2
    · subst i; exact hv
    · have hn : Impl.AesGcm.PPC64LE.Blocks.reg i ≠ Impl.AesGcm.PPC64LE.Blocks.reg (j+2) := by
        intro hx
        exact he (state_injective ⟨i,by omega⟩ ⟨j+2,by omega⟩ hx)
      rw [cipherAt,hf.v _ (by simpa only [List.mem_singleton] using hn)]
      exact hs.value i (by omega)

theorem counterSteps_ok (base : State) (cb : Spec.Gcm.Block)
    (ht : base.vpr T=0#96++2#32)
    (hv : ∀ i < 2, cipherAt base i=Nat.repeat Spec.Gcm.inc32 i cb) :
    WP isa (.block ((List.range 6).flatMap (fun j =>
      [.vop (.add false (Impl.AesGcm.PPC64LE.Blocks.reg (j+2))
        (Impl.AesGcm.PPC64LE.Blocks.reg j) T)]))) base (CounterStepsInv base cb 6) := by
  exact wp_range_flatMap (M := isa) (CounterStepsInv base cb)
    (fun j t hj hs => counterSteps_step ht hj hs) 6 (Nat.le_refl _) base ⟨VOnly.refl _ _,hv⟩


structure CounterStartResult (base : State) (cb : Spec.Gcm.Block) (s : State) : Prop where
  effects : VOnly [.v0,U,T,.v1] base s
  first : s.vpr .v0=cb
  second : s.vpr .v1=Spec.Gcm.inc32 cb
  one : s.vpr U=0#96++1#32
  two : s.vpr T=0#96++2#32

theorem counterStart_ok (base : State) (cb : Spec.Gcm.Block)
    (hrc : InRegions (base.rd++base.wr) (base.gpr .r16+base.gpr .r15) 16)
    (hr1 : InRegions (base.rd++base.wr) (base.gpr .r16+base.gpr .r20) 16)
    (hc : swapDwords (base.mem.read (base.gpr .r16+base.gpr .r15) 16)=cb)
    (h1 : swapDwords (base.mem.read (base.gpr .r16+base.gpr .r20) 16)=0#96++1#32) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.counterStart) base (CounterStartResult base cb) := by
  have he : Impl.AesGcm.PPC64LE.Blocks.counterStart =
      ([.lxvd2x .v0 .r16 .r15] : List Instr) ++ [.lxvd2x U .r16 .r20] ++
      [.vop (.add false T U U)] ++ [.vop (.add false .v1 .v0 U)] := rfl
  rw [he,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (rawLoad_ok .v0 .r16 .r15 base (by decide) hrc) fun u ⟨hu,hf⟩ => ?_
  have hr1' : InRegions (u.rd++u.wr) (u.gpr .r16+u.gpr .r20) 16 := by
    simpa only [hf.rd,hf.wr,hf.gpr] using hr1
  refine WP.mono (rawLoad_ok U .r16 .r20 u (by decide) hr1') fun v ⟨hv,hg⟩ => ?_
  have hv1 : v.vpr U=0#96++1#32 := by
    rw [hv,hf.mem,hf.gpr]; exact h1
  have hv0 : v.vpr .v0=cb := (hg.v .v0 (by decide)).trans (hu.trans hc)
  refine WP.mono (vector_step (.vop (.add false T U U)) T _ v
    (exec_add_counter T U U 1 v hv1)) fun w ⟨hw,hh⟩ => ?_
  have hw2 : w.vpr T=0#96++2#32 := by rw [hw,hv1]; rfl
  have hw1 : w.vpr U=0#96++1#32 := (hh.v U (by decide)).trans hv1
  have hw0 : w.vpr .v0=cb := (hh.v .v0 (by decide)).trans hv0
  refine WP.mono (vector_step (.vop (.add false .v1 .v0 U)) .v1 _ w
    (exec_add_counter .v1 .v0 U 1 w hw1)) fun t ⟨ht,hi⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((hf.trans hg).trans hh).trans hi).weaken (by simp)
  · exact (hi.v .v0 (by decide)).trans hw0
  · rw [ht,hw0]; rfl
  · exact (hi.v U (by decide)).trans hw1
  · exact (hi.v T (by decide)).trans hw2


structure CounterNextResult (base : State) (cb : Spec.Gcm.Block) (s : State) : Prop where
  keep : Keep [.r8] base s
  v : ∀ r, r ≠ T → s.vpr r=base.vpr r
  value : s.vpr T=Nat.repeat Spec.Gcm.inc32 8 cb
  scalar : s.gpr .r8=base.gpr .r8+8
  mem : s.mem=base.mem.write (base.gpr .r16+base.gpr .r15) 16
    (swapDwords (Nat.repeat Spec.Gcm.inc32 8 cb))

theorem counterNext_ok (base : State) (cb : Spec.Gcm.Block)
    (ht : base.vpr T=0#96++2#32)
    (hv : cipherAt base 6=Nat.repeat Spec.Gcm.inc32 6 cb)
    (hw : InRegions base.wr (base.gpr .r16+base.gpr .r15) 16) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.counterNext 8)) base (CounterNextResult base cb) := by
  have he : Impl.AesGcm.PPC64LE.Blocks.counterNext 8 =
      ([.vop (.add false T .v6 T)] : List Instr) ++ [.stxvd2x T .r16 .r15] ++ [.addi .r8 .r8 8] := rfl
  rw [he,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (vector_step (.vop (.add false T .v6 T)) T _ base
    (exec_add_counter T .v6 T 2 base ht)) fun u ⟨hu,hf⟩ => ?_
  have hval : u.vpr T=Nat.repeat Spec.Gcm.inc32 8 cb := by
    rw [hu,← counter_advance cb 6 2,← hv]
    rfl
  have hw' : InRegions u.wr (u.gpr .r16+u.gpr .r15) 16 := by
    simpa only [hf.wr,hf.gpr] using hw
  refine WP.mono (rawStore_ok T .r16 .r15 u (by decide) hw') fun w hw => ?_
  subst w
  have hadd : WP isa (.block ([.addi .r8 .r8 8] : List Instr))
      {u with mem := u.mem.write (u.gpr .r16+u.gpr .r15) 16 (swapDwords (u.vpr T))}
      (· = {u with mem := u.mem.write (u.gpr .r16+u.gpr .r15) 16 (swapDwords (u.vpr T))}.write .r8 (u.gpr .r8+8)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,
      exec_addi (n := .r8) (imm := 8) (by decide) (by decide),Option.some.injEq,exists_eq_left']
    rfl
  refine WP.mono hadd fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rw [RegUpd.gpr_write,ite_eq_right (by simpa only [List.mem_singleton] using hr)]
      exact congrFun hf.gpr r
    · exact (RegUpd.rd_write ..).trans hf.rd
    · exact (RegUpd.wr_write ..).trans hf.wr
  · intro r hr
    simpa only [vpr_write] using hf.v r (by simpa only [List.mem_singleton] using hr)
  · simpa only [vpr_write] using hval
  · simp only [RegUpd.gpr_write_self,hf.gpr]
  · simp only [RegUpd.mem_write,hval,hf.mem,hf.gpr]


structure CountersResult (base : State) (cb : Spec.Gcm.Block) (s : State) : Prop where
  keep : Keep [.r8] base s
  v : ∀ r, r ∉ Impl.AesGcm.PPC64LE.Blocks.rs 8 ++ [U,T] → s.vpr r=base.vpr r
  values : ∀ i < 8, cipherAt s i=Nat.repeat Spec.Gcm.inc32 i cb
  scalar : s.gpr .r8=base.gpr .r8+8
  mem : s.mem=base.mem.write (base.gpr .r16+base.gpr .r15) 16
    (swapDwords (Nat.repeat Spec.Gcm.inc32 8 cb))

theorem counters_ok (base : State) (cb : Spec.Gcm.Block)
    (hrc : InRegions (base.rd++base.wr) (base.gpr .r16+base.gpr .r15) 16)
    (hr1 : InRegions (base.rd++base.wr) (base.gpr .r16+base.gpr .r20) 16)
    (hw : InRegions base.wr (base.gpr .r16+base.gpr .r15) 16)
    (hc : swapDwords (base.mem.read (base.gpr .r16+base.gpr .r15) 16)=cb)
    (h1 : swapDwords (base.mem.read (base.gpr .r16+base.gpr .r20) 16)=0#96++1#32) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.counters 8)) base (CountersResult base cb) := by
  have he : Impl.AesGcm.PPC64LE.Blocks.counters 8 =
      Impl.AesGcm.PPC64LE.Blocks.counterStart ++
      (List.range 6).flatMap (fun j => [.vop (.add false (Impl.AesGcm.PPC64LE.Blocks.reg (j+2))
        (Impl.AesGcm.PPC64LE.Blocks.reg j) T)]) ++ Impl.AesGcm.PPC64LE.Blocks.counterNext 8 := rfl
  rw [he,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (counterStart_ok base cb hrc hr1 hc h1) fun s hs => ?_
  have hs01 : ∀ i < 2, cipherAt s i=Nat.repeat Spec.Gcm.inc32 i cb := by
    intro i hi
    by_cases hz : i=0
    · subst i; exact hs.first
    · have hi1 : i=1 := by omega
      subst i; exact hs.second
  refine WP.mono (counterSteps_ok s cb hs.two hs01) fun u hu => ?_
  have hg : u.gpr=base.gpr := hu.effects.gpr.trans hs.effects.gpr
  have hm : u.mem=base.mem := hu.effects.mem.trans hs.effects.mem
  have hwr : u.wr=base.wr := hu.effects.wr.trans hs.effects.wr
  have htwo : u.vpr T=0#96++2#32 := (hu.effects.v T (by decide)).trans hs.two
  have hw' : InRegions u.wr (u.gpr .r16+u.gpr .r15) 16 := by rw [hwr,hg]; exact hw
  refine WP.mono (counterNext_ok u cb htwo (hu.value 6 (by decide)) hw') fun t ht => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun r hr => (ht.keep.gpr hr).trans (congrFun hg r),
      ht.keep.2.1.trans (hu.effects.rd.trans hs.effects.rd),ht.keep.2.2.trans hwr⟩
  · intro r hr
    have hsplit : r ∉ Impl.AesGcm.PPC64LE.Blocks.rs 8 ∧ r ∉ [U,T] := by
      simpa only [List.mem_append,not_or] using hr
    have hufree := hsplit.1
    have hutfree := hsplit.2
    have htfree : r ≠ T := fun he => hutfree (List.mem_cons_of_mem _ (List.mem_singleton.mpr he))
    have hsfree : r ∉ [.v0,U,T,.v1] := by
      intro hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with h | h | h | h
      · subst r; exact hufree (by decide)
      · subst r; exact hutfree (by decide)
      · subst r; exact hutfree (by decide)
      · subst r; exact hufree (by decide)
    exact (ht.v r htfree).trans ((hu.effects.v r hufree).trans (hs.effects.v r hsfree))
  · intro i hi
    have hfree : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ≠ T := by decide
    change t.vpr (Impl.AesGcm.PPC64LE.Blocks.reg i)=_
    rw [ht.v _ (hfree ⟨i,hi⟩)]
    exact hu.value i hi
  · rw [ht.scalar,hg]
  · rw [ht.mem,hm,hg]


theorem keyOffset_ok (i : Fin 8) (s : State)
    (known : Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      s.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1))) :
    WP isa (.block (if Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs.contains
      (Impl.AesGcm.PPC64LE.Blocks.keyOffset i) then
      [.li (Impl.AesGcm.PPC64LE.Blocks.keyOffset i) (16*(i+1))] else [])) s fun t =>
      t.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1)) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs [] s t ∧
      (∀ r, r ≠ Impl.AesGcm.PPC64LE.Blocks.keyOffset i → t.gpr r=s.gpr r) := by
  by_cases hs : Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs.contains
      (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=true
  · rw [ite_eq_left hs]
    have he : WP isa (.block ([.li (Impl.AesGcm.PPC64LE.Blocks.keyOffset i) (16*(i+1))] : List Instr)) s
        (· = s.write (Impl.AesGcm.PPC64LE.Blocks.keyOffset i) (BitVec.ofNat 64 (16*(i+1)))) := by
      apply WP.of_runBlock
      simp only [runBlock_cons,runStep_some,runBlock_nil,exec_li (imm := 16*(i+1)) (by omega),Option.some.injEq,exists_eq_left']
    refine WP.mono he fun t ht => ?_
    subst t
    exact ⟨RegUpd.gpr_write_self ..,
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write s _ _).weaken
        (by simpa only [List.mem_singleton,forall_eq] using List.contains_iff_mem.mp hs) (by simp),
      fun r hr => by rw [RegUpd.gpr_write,ite_eq_right hr]⟩
  · rw [ite_eq_right hs]
    exact WP.block_nil ⟨known (fun hm => hs (List.contains_iff_mem.mpr hm)),
      VG.Proof.Aes.PPC64LE.Crypto.Local.refl _ _ _,fun _ _ => rfl⟩

theorem keyRead_ok (i : Fin 8) (s : State)
    (known : Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      s.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1)))
    (hr : InRegions (s.rd++s.wr) (s.gpr .r3+BitVec.ofNat 64 (16*(i+1))) 16) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.keyRead i)) s fun t =>
      t.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i)=
        swapDwords (s.mem.read (s.gpr .r3+BitVec.ofNat 64 (16*(i+1))) 16) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs
        [Impl.AesGcm.PPC64LE.Blocks.dataReg i] s t ∧
      t.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1)) ∧
      (∀ r, r ≠ Impl.AesGcm.PPC64LE.Blocks.keyOffset i → t.gpr r=s.gpr r) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.keyRead,WP.block_append_iff]
  refine WP.mono (keyOffset_ok i s known) fun u ⟨hu,hf,hothers⟩ => ?_
  have hp : u.gpr .r3=s.gpr .r3 := hf.keep.gpr (by decide)
  have hr' : InRegions (u.rd++u.wr) (u.gpr .r3+u.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)) 16 := by
    rw [hf.keep.2.1,hf.keep.2.2,hp,hu]; exact hr
  refine WP.mono (rawLoad_ok (Impl.AesGcm.PPC64LE.Blocks.dataReg i) .r3 _ u (by decide) hr')
    fun t ⟨ht,hg⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [ht,hf.mem,hp,hu]
  · exact (hf.trans (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hg)).weaken (by simp) (by simp)
  · rw [hg.gpr]; exact hu
  · intro r hr; rw [hg.gpr]; exact hothers r hr


structure PreloadInv (base : State) (w : List Byte) (j : Nat) (s : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs
    Impl.AesGcm.PPC64LE.Blocks.dataRegs base s
  keys : ∀ i < j, VG.Proof.Aes.PPC64LE.Crypto.IsKey
    (s.vpr (Impl.AesGcm.PPC64LE.Blocks.dataReg i)) (Spec.Aes.roundKey w (i+1))
  offsets : ∀ i < j, s.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1))

theorem preload_step {base : State} {nr : Nat} {w : List Byte} (cfg : RawCfg base nr w)
    (known : ∀ i < 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      base.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1)))
    {j : Nat} (hj : j<8) {s : State} (hs : PreloadInv base w j s) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.keyRead j)) s (PreloadInv base w (j+1)) := by
  have hk : Impl.AesGcm.PPC64LE.Blocks.keyOffset j ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      s.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset j)=BitVec.ofNat 64 (16*(j+1)) := by
    intro hn
    rw [hs.effects.keep.gpr hn]; exact known j hj hn
  have hr : InRegions (s.rd++s.wr) (s.gpr .r3+BitVec.ofNat 64 (16*(j+1))) 16 := by
    rw [hs.effects.keep.2.1,hs.effects.keep.2.2,hs.effects.keep.gpr (by decide)]
    exact cfg.reads (j+1) (by have := cfg.min; omega)
  refine WP.mono (keyRead_ok ⟨j,hj⟩ s hk hr) fun t ⟨hv,hf,hoff,hothers⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · exact (hs.effects.trans hf).weaken (by simp) (by
      intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact h
      · rw [List.mem_singleton] at h
        subst r
        have hm : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.dataReg i ∈ Impl.AesGcm.PPC64LE.Blocks.dataRegs := by decide
        exact hm ⟨j,hj⟩)
  · intro i hi
    by_cases he : i=j
    · subst i
      rw [hv,hs.effects.mem,hs.effects.keep.gpr (by decide)]
      exact cfg.keys (j+1) (by have := cfg.min; omega)
    · have hn : Impl.AesGcm.PPC64LE.Blocks.dataReg i ≠ Impl.AesGcm.PPC64LE.Blocks.dataReg j :=
        fun hx => he (data_injective ⟨i,by omega⟩ ⟨j,hj⟩ hx)
      rw [hf.v _ (by simpa only [List.mem_singleton] using hn)]
      exact hs.keys i (by omega)
  · intro i hi
    by_cases he : i=j
    · subst i; exact hoff
    · have inj : ∀ i j : Fin 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i =
          Impl.AesGcm.PPC64LE.Blocks.keyOffset j → i.val=j.val := by decide
      rw [hothers _ (fun hx => he (inj ⟨i,by omega⟩ ⟨j,hj⟩ hx))]
      exact hs.offsets i (by omega)


theorem preloadEight_ok (base : State) (nr : Nat) (w : List Byte) (cfg : RawCfg base nr w)
    (known : ∀ i < 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      base.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1))) :
    WP isa (.block ((List.range 8).flatMap Impl.AesGcm.PPC64LE.Blocks.keyRead)) base (PreloadInv base w 8) := by
  exact wp_range_flatMap (M := isa) (PreloadInv base w)
    (fun j t hj hs => preload_step cfg known hj hs) 8 (Nat.le_refl _) base
    ⟨VG.Proof.Aes.PPC64LE.Crypto.Local.refl _ _ _,fun _ hi => False.elim (by omega),
      fun _ hi => False.elim (by omega)⟩


def DataOffsets (s : State) : Prop :=
  ∀ i < 8, s.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset i)=BitVec.ofNat 64 (16*i)

theorem keyReads_ok (base : State) (nr : Nat) (w : List Byte) (cfg : RawCfg base nr w)
    (known : ∀ i < 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      base.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1))) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.keyReads) base fun t =>
      (∀ j < 9, VG.Proof.Aes.PPC64LE.Crypto.IsKey (t.vpr (keyReg j)) (Spec.Aes.roundKey w (j+1))) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local (.r9 :: Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs)
        (Impl.AesGcm.PPC64LE.Blocks.dataRegs++[T]) base t ∧ DataOffsets t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.keyReads,WP.block_append_iff]
  refine WP.mono (preloadEight_ok base nr w cfg known) fun s hs => ?_
  have he : ([.addi .r9 .r3 144,.lxvd2x T .r9 .r0] : List Instr) =
      [.addi .r9 .r3 144] ++ [.lxvd2x T .r9 .r0] := rfl
  rw [he,WP.block_append_iff]
  have hm : WP isa (.block ([.addi .r9 .r3 144] : List Instr)) s
      (· = s.write .r9 (s.gpr .r3+144)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,
      exec_addi (n := .r3) (imm := 144) (by decide) (by decide),Option.some.injEq,exists_eq_left']
    rfl
  refine WP.mono hm fun u hu => ?_
  subst u
  have hp : s.gpr .r3=base.gpr .r3 := hs.effects.keep.gpr (by decide)
  have hz : s.gpr .r0=0 := (hs.effects.keep.gpr (by decide)).trans cfg.zero
  have hr : InRegions ((s.write .r9 (s.gpr .r3+144)).rd++(s.write .r9 (s.gpr .r3+144)).wr)
      ((s.write .r9 (s.gpr .r3+144)).gpr .r9+(s.write .r9 (s.gpr .r3+144)).gpr .r0) 16 := by
    simp only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,
      hs.effects.keep.2.1,hs.effects.keep.2.2,hp,hz,BitVec.ofNat_eq_ofNat,BitVec.add_zero]
    exact cfg.reads 9 (by have := cfg.min; omega)
  refine WP.mono (rawLoad_ok T .r9 .r0 _ (by decide) hr) fun t ⟨hv,hf⟩ => ?_
  have hT : VG.Proof.Aes.PPC64LE.Crypto.IsKey (t.vpr T) (Spec.Aes.roundKey w 9) := by
    rw [hv]
    simp only [RegUpd.mem_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,
      hs.effects.mem,hp,hz,BitVec.ofNat_eq_ofNat,BitVec.add_zero]
    exact cfg.keys 9 (by have := cfg.min; omega)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    by_cases heq : j=8
    · subst j; exact hT
    · have hj8 : j<8 := by omega
      have hmap : ∀ i : Fin 8, keyReg i=Impl.AesGcm.PPC64LE.Blocks.dataReg i := by decide
      have hfree : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.dataReg i ≠ T := by decide
      rw [hmap ⟨j,hj8⟩,hf.v _ (by simpa only [List.mem_singleton] using hfree ⟨j,hj8⟩),vpr_write]
      exact hs.keys j hj8
  · have heffects := (hs.effects.trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write s .r9 (s.gpr .r3+144))).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hf)
    exact heffects.weaken (by simp [or_comm]) (by simp)
  · intro i hi
    have hfree : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.dataOffset i ≠ .r9 := by decide
    rw [hf.gpr,RegUpd.gpr_write,ite_eq_right (hfree ⟨i,hi⟩)]
    by_cases hz0 : i=0
    · subst i; exact hz
    · have hi' : i-1<7 := by omega
      have hmap : ∀ j : Fin 7, Impl.AesGcm.PPC64LE.Blocks.dataOffset (j+1)=
          Impl.AesGcm.PPC64LE.Blocks.keyOffset j := by decide
      have hie : i=(i-1)+1 := by omega
      rw [hie,hmap ⟨i-1,hi'⟩,hs.offsets (i-1) (by omega)]


theorem firstNine_ok (base : State) (nr : Nat) (w : List Byte) (input : Nat → Spec.Aes.State)
    (cfg : RawCfg base nr w)
    (known : ∀ i < 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      base.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1)))
    (values : ∀ i < 8, aesState (cipherAt base i)=
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 0) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.firstNine) base fun t =>
      (∀ i < 8, aesState (cipherAt t i)=VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 9) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local (.r9 :: Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs)
        (Impl.AesGcm.PPC64LE.Blocks.dataRegs++[T]++Impl.AesGcm.PPC64LE.Blocks.rs 8) base t ∧ DataOffsets t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.firstNine,WP.block_append_iff]
  refine WP.mono (keyReads_ok base nr w cfg known) fun s ⟨hk,hf,hoff⟩ => ?_
  have hv : ∀ i < 8, aesState (cipherAt s i)=
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 0 := by
    intro i hi
    have free : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ∉
        Impl.AesGcm.PPC64LE.Blocks.dataRegs++[T] := by decide
    rw [cipherAt,hf.v _ (free ⟨i,hi⟩)]
    exact values i hi
  refine WP.mono (keyRounds_ok nr w input s hk hv) fun t ht => ?_
  exact ⟨ht.val,(hf.trans (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector ht.effects)).weaken
    (by simp) (by simp),by intro i hi; rw [ht.effects.gpr]; exact hoff i hi⟩


theorem aesInitial_ok (base : State) (nr : Nat) (w : List Byte) (cfg : RawCfg base nr w) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.aesInitial) base fun t =>
      (∀ i < 8, aesState (cipherAt t i)=VG.Proof.Aes.PPC64LE.Crypto.middle false nr w
        (aesState (cipherAt base i)) 0) ∧
      VOnly (.v8 :: Impl.AesGcm.PPC64LE.Blocks.rs 8) base t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.aesInitial,WP.block_append_iff]
  have hr : InRegions (base.rd++base.wr) (base.gpr .r3+base.gpr .r0) 16 := by
    simpa only [cfg.zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero,Nat.mul_zero] using cfg.reads 0 (by omega)
  refine WP.mono (rawLoad_ok .v8 .r3 .r0 base (by decide) hr) fun s ⟨hv,hf⟩ => ?_
  have hkey : VG.Proof.Aes.PPC64LE.Crypto.IsKey (s.vpr .v8) (Spec.Aes.roundKey w 0) := by
    rw [hv]
    simpa only [cfg.zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero,Nat.mul_zero] using cfg.keys 0 (by omega)
  refine WP.mono (vector_map (fun b => .vop (.logic .xor b b .v8)) (· ^^^ ·) .v8 (fun _ _ => rfl)
    (Impl.AesGcm.PPC64LE.Blocks.rs 8) s (by decide) (by decide)) fun t ⟨ht,hg⟩ => ?_
  refine ⟨?_,hf.trans hg⟩
  intro i hi
  have hm : Impl.AesGcm.PPC64LE.Blocks.reg i ∈ Impl.AesGcm.PPC64LE.Blocks.rs 8 :=
    List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have hn : Impl.AesGcm.PPC64LE.Blocks.reg i ≠ .v8 := by
    have free : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ≠ .v8 := by decide
    exact free ⟨i,hi⟩
  rw [cipherAt,ht _ hm,VG.Proof.Aes.PPC64LE.Crypto.xor_state hkey,
    hf.v _ (by simpa only [List.mem_singleton] using hn)]
  exact (VG.Proof.Aes.PPC64LE.Crypto.middle_zero false nr w (aesState (cipherAt base i))).symm

theorem RawCfg.of_local {base s : State} {nr : Nat} {w : List Byte}
    {gs : List Reg} {vs : List VReg} (cfg : RawCfg base nr w)
    (hs : VG.Proof.Aes.PPC64LE.Crypto.Local gs vs base s)
    (h0 : .r0 ∉ gs) (h3 : .r3 ∉ gs) : RawCfg s nr w := by
  refine ⟨(hs.keep.gpr h0).trans cfg.zero,cfg.min,cfg.max,?_,?_⟩
  · intro j hj
    rw [hs.keep.2.1,hs.keep.2.2,hs.keep.gpr h3]; exact cfg.reads j hj
  · intro j hj
    rw [hs.mem,hs.keep.gpr h3]; exact cfg.keys j hj

theorem aesRemaining_ok (base : State) (nr : Nat) (w : List Byte)
    (input : Nat → Spec.Aes.State) (cfg : RawCfg base nr w)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr)
    (values : ∀ i < 8, aesState (cipherAt base i)=VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 9) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.aesRemaining) base (RawInv base nr w input 9) := by
  have he : WP isa (.block Impl.AesGcm.PPC64LE.Blocks.aesRemaining) base
      (· = (base.write .r9 (base.gpr .r3+160)).write .r10 (base.gpr .r4-10)) := by
    apply WP.of_runBlock
    simp only [Impl.AesGcm.PPC64LE.Blocks.aesRemaining,runBlock_cons,runStep_some,runBlock_nil,
      exec_addi (n := .r3) (imm := 160) (by decide) (by decide),
      exec_subi (n := .r4) (imm := 10) (by decide) (by decide),RegUpd.gpr_write,
      reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
    rfl
  refine WP.mono he fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((VG.Proof.Aes.PPC64LE.Crypto.Local.write base .r9 (base.gpr .r3+160)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r10 (base.gpr .r4-10))).weaken (by simp) (by simp)
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
    rfl
  · simp only [RegUpd.gpr_write_self,hr]
    change BitVec.ofNat 64 nr-BitVec.ofNat 64 10=_
    rw [Offset.ofNat_sub_ofNat (by have := cfg.min; omega)]
    congr 1
  · intro i hi
    simpa only [cipherAt,vpr_write] using values i hi


theorem aes8_ok (base : State) (nr : Nat) (w : List Byte) (cfg : RawCfg base nr w)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr)
    (known : ∀ i < 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      base.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1))) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.aes8 base fun t =>
      (∀ i < 8, aesState (cipherAt t i)=Spec.Aes.cipher nr w (aesState (cipherAt base i))) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local (([.r9,.r10] : List Reg)++Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs)
        (.v8 :: (Impl.AesGcm.PPC64LE.Blocks.rs 8++Impl.AesGcm.PPC64LE.Blocks.dataRegs++[T])) base t ∧ DataOffsets t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.aes8]
  apply WP.seq
  rw [WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (aesInitial_ok base nr w cfg) fun s ⟨hv,hf⟩ => ?_
  have cfgs : RawCfg s nr w := cfg.of_local (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hf) (by simp) (by simp)
  have knowns : ∀ i < 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      s.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1)) := by
    intro i hi hn
    rw [hf.gpr]; exact known i hi hn
  refine WP.mono (firstNine_ok s nr w (fun i => aesState (cipherAt base i)) cfgs knowns hv)
    fun u ⟨hu,hg,hoff⟩ => ?_
  have cfgu : RawCfg u nr w := cfgs.of_local hg (by decide) (by decide)
  have hru : u.gpr .r4=BitVec.ofNat 64 nr :=
    (hg.keep.gpr (by decide)).trans ((congrFun hf.gpr .r4).trans hr)
  refine WP.mono (aesRemaining_ok u nr w (fun i => aesState (cipherAt base i)) cfgu hru hu)
    fun v hv => ?_
  apply WP.seq
  refine WP.mono (remaining_ok cfgu (show 9 ≤ nr-1 by have := cfg.min; omega) hv) fun z hz => ?_
  refine WP.mono (raw_last_ok cfgu hz) fun t ⟨ht,he⟩ => ?_
  refine ⟨ht, ?_, ?_⟩
  · exact (((VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hf).trans hg).trans he).weaken
      (by simp [or_left_comm,or_comm,or_assoc]) (by simp [or_left_comm,or_comm,or_assoc])
  · intro i hi
    have hfree : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.dataOffset i ∉ [.r9,.r10] := by decide
    rw [he.keep.gpr (hfree ⟨i,hi⟩)]
    exact hoff i hi


def ciphertextValue (base : State) (i : Nat) : BitVec 128 :=
  cipherAt base i ^^^ rev128 (base.mem.read (base.gpr .r6+BitVec.ofNat 64 (16*i)) 16)

structure StoreBatchResult (base : State) (m₀ : Mem) (D : Addr) (n k : Nat)
    (F : Nat → Spec.Aes.State) (s : State) : Prop where
  keep : Keep [.r6,.r7] base s
  v : ∀ r, r ∉ mixRegs → s.vpr r=base.vpr r
  processed : VG.Proof.Aes.Memory.Processed m₀ s.mem D n (k+8) F
  frame : Frame [⟨D,16*n⟩] base.mem s.mem
  values : ∀ i < 8, cipherAt s i=ciphertextValue base i
  ptr : s.gpr .r6=base.gpr .r6+128
  left : s.gpr .r7=base.gpr .r7-8

theorem storesAdvance_ok (s : State) :
    WP isa (.block ([.addi .r6 .r6 128,.subi .r7 .r7 8] : List Instr)) s
      (· = (s.write .r6 (s.gpr .r6+128)).write .r7 (s.gpr .r7-8)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,
    exec_addi (n := .r6) (imm := 128) (by decide) (by decide),
    exec_subi (n := .r7) (imm := 8) (by decide) (by decide),RegUpd.gpr_write,
    reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl

theorem stores_ok (base : State) (m₀ : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State)
    (hkn : k+8 ≤ n) (hsize : 16*n ≤ 2^64)
    (hm : base.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask)
    (ptr : base.gpr .r6=D+BitVec.ofNat 64 (16*k))
    (offsets : ∀ i < 8, base.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset i)=BitVec.ofNat 64 (16*i))
    (reads : ∀ i < 8, InRegions (base.rd++base.wr) (base.gpr .r6+BitVec.ofNat 64 (16*i)) 16)
    (writes : ∀ i < 8, InRegions base.wr (D+BitVec.ofNat 64 (16*(k+i))) 16)
    (values : ∀ i < 8, aesState (ciphertextValue base i)=F (k+i))
    (processed : VG.Proof.Aes.Memory.Processed m₀ base.mem D n k F) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.stores) base (StoreBatchResult base m₀ D n k F) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.stores,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (dataLoad_ok base offsets reads) fun s hs => ?_
  have hmask : s.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask := (hs.effects.v _ (by decide)).trans hm
  refine WP.mono (dataMix_ok s hmask) fun u hu => ?_
  have hgp : u.gpr=base.gpr := hu.effects.gpr.trans hs.effects.gpr
  have hmem : u.mem=base.mem := hu.effects.mem.trans hs.effects.mem
  have hwr : u.wr=base.wr := hu.effects.wr.trans hs.effects.wr
  have hvals : ∀ i < 8, cipherAt u i=ciphertextValue base i := by
    intro i hi
    have hr : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ∉ Impl.AesGcm.PPC64LE.Blocks.dataRegs := by decide
    have hv := hu.val ⟨i,hi⟩
    change cipherAt u i=if i<8 then mixValue s i else cipherAt s i at hv
    rw [ite_eq_left hi] at hv
    rw [hv,mixValue,hs.val i hi,VG.Proof.Aes.PPC64LE.Crypto.flip_load]
    rw [cipherAt,hs.effects.v _ (hr ⟨i,hi⟩)]
    rfl
  have masku : u.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask :=
    (hu.effects.v _ (by decide)).trans hmask
  have processedu : VG.Proof.Aes.Memory.Processed m₀ u.mem D n k F := by rw [hmem]; exact processed
  have ptru : u.gpr .r6=D+BitVec.ofNat 64 (16*k) := by rw [hgp]; exact ptr
  have offu : ∀ i < 8, u.gpr (Impl.AesGcm.PPC64LE.Blocks.dataOffset i)=BitVec.ofNat 64 (16*i) := by
    intro i hi; rw [hgp]; exact offsets i hi
  have wru : ∀ i < 8, InRegions u.wr (D+BitVec.ofNat 64 (16*(k+i))) 16 := by
    intro i hi; rw [hwr]; exact writes i hi
  have valu : ∀ i < 8, aesState (cipherAt u i)=F (k+i) := by
    intro i hi; rw [hvals i hi]; exact values i hi
  refine WP.mono (dataWrite_ok u m₀ D n k F hkn hsize masku ptru offu wru valu processedu) fun v hv => ?_
  have hvgp : v.gpr=base.gpr := (funext fun r => hv.keep.gpr (by simp)).trans hgp
  refine WP.mono (storesAdvance_ok v) fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he := ((VG.Proof.Aes.PPC64LE.Crypto.Local.write v .r6 (v.gpr .r6+128)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r7 (v.gpr .r7-8))).keep
    exact ⟨fun r hr => (he.gpr hr).trans (congrFun hvgp r),
      he.2.1.trans (hv.keep.2.1.trans (hu.effects.rd.trans hs.effects.rd)),
      he.2.2.trans (hv.keep.2.2.trans hwr)⟩
  · intro r hr
    have hdfree : r ∉ Impl.AesGcm.PPC64LE.Blocks.dataRegs :=
      fun hx => hr (List.mem_append_left _ hx)
    simpa only [vpr_write] using (hv.v r hdfree).trans
      ((hu.effects.v r hr).trans (hs.effects.v r hdfree))
  · simpa only [RegUpd.mem_write] using hv.processed
  · simpa only [RegUpd.mem_write,hmem] using hv.frame
  · intro i hi
    have hfree : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ∉ Impl.AesGcm.PPC64LE.Blocks.dataRegs := by decide
    simpa only [cipherAt,vpr_write,hv.v _ (hfree ⟨i,hi⟩)] using hvals i hi
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false,hvgp]
  · simp only [RegUpd.gpr_write_self,hvgp]


theorem cachedKey_isKey {base s : State} {count j : Nat} {w : List Byte}
    (hs : CacheInv base count count s) (hj : j<count)
    (hk : VG.Proof.Aes.PPC64LE.Crypto.IsKey
      (rev128 (base.mem.read (base.gpr .r9+BitVec.ofNat 64 (16*j)) 16)) (Spec.Aes.roundKey w j)) :
    VG.Proof.Aes.PPC64LE.Crypto.IsKey
      (swapDwords (s.mem.read (base.gpr .r11+BitVec.ofNat 64 (16*j)) 16)) (Spec.Aes.roundKey w j) := by
  rw [cachedKey_read hs hj,cachedKey,swapDwords_involutive]
  exact hk

theorem powerCopy_ok (j : Nat) (s : State) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.powerCopy j)) s fun t =>
      t.vpr .v8=(if (j+2)%2=0 then s.vpr .v12 else s.vpr .v8) ∧ VOnly [.v8] s t := by
  by_cases he : (j+2)%2=0
  · rw [Impl.AesGcm.PPC64LE.Blocks.powerCopy,ite_eq_left he]
    refine WP.mono (vector_step (.vop (.logic .or .v8 .v12 .v12)) .v8 _ s
      (exec_copyVector .v8 .v12 s)) fun t ⟨hv,hf⟩ => ?_
    exact ⟨by rw [ite_eq_left he]; exact hv,hf⟩
  · rw [Impl.AesGcm.PPC64LE.Blocks.powerCopy,ite_eq_right he]
    exact WP.block_nil ⟨by rw [ite_eq_right he],VOnly.refl _ _⟩

theorem powerNext_ok (j : Nat) (h : BitVec 128) (s : State)
    (hv : s.vpr .v12=VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h j)
    (hk : s.vpr .v11=h) (hc : s.vpr .v13=poly++poly) (hz : s.vpr .v0=0) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.powerNext j)) s fun t =>
      t.vpr .v12=VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (j+1) ∧
      t.vpr .v8=(if (j+2)%2=0 then VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h j else s.vpr .v8) ∧
      VOnly [.v8,.v9,U,LO,MID,HI,T,.v12] s t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.powerNext,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (powerCopy_ok j s) fun u ⟨hu,hf⟩ => ?_
  refine WP.mono (vector_step (.vop (.sldoi .v9 .v12 .v12 8)) .v9 _ u
    (VG.Proof.Gcm.PPC64LE.Vpmsum.exec_shift8 .v9 .v12 .v12 u)) fun v ⟨hval,hg⟩ => ?_
  have ha : v.vpr .v9=VG.Proof.Gcm.Clmul.ext8 (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h j)
      (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h j) := by
    rw [hval,VG.Proof.Gcm.PPC64LE.Vpmsum.half_self,hf.v .v12 (by decide),hv]
  have hc' : v.vpr .v13=poly++poly := ((hg.v .v13 (by decide)).trans (hf.v .v13 (by decide))).trans hc
  have hz' : v.vpr .v0=0 := ((hg.v .v0 (by decide)).trans (hf.v .v0 (by decide))).trans hz
  have hk' : v.vpr .v11=h := ((hg.v .v11 (by decide)).trans (hf.v .v11 (by decide))).trans hk
  refine WP.mono (mul_ok .v12 .v9 .v11 v (by decide) (by decide) hc' hz') fun w ⟨hw,hh⟩ => ?_
  refine WP.mono (vector_step (.vop (.sldoi .v12 .v12 .v12 8)) .v12 _ w
    (VG.Proof.Gcm.PPC64LE.Vpmsum.exec_shift8 .v12 .v12 .v12 w)) fun t ⟨ht,hi⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht,VG.Proof.Gcm.PPC64LE.Vpmsum.half_self,hw,ha,hk']
    rfl
  · rw [hi.v .v8 (by decide),hh.v .v8 (by decide),hg.v .v8 (by decide),hu,hv]
  · exact (((hf.trans hg).trans hh).trans hi).weaken (by simp [or_left_comm])


theorem powerSave_ok (v : VReg) (offset : Nat) (s : State) (ho : offset<2^15)
    (hw : InRegions s.wr (s.gpr .r16+BitVec.ofNat 64 offset) 16) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.powerSave v offset)) s
      (· = {s.write .r11 (BitVec.ofNat 64 offset) with
        mem := s.mem.write (s.gpr .r16+BitVec.ofNat 64 offset) 16 (swapDwords (s.vpr v))}) := by
  have he : Impl.AesGcm.PPC64LE.Blocks.powerSave v offset =
      ([.li .r11 offset] : List Instr) ++ [.stxvd2x v .r16 .r11] := rfl
  rw [he,WP.block_append_iff]
  have hli : WP isa (.block ([.li .r11 offset] : List Instr)) s (· = s.write .r11 (BitVec.ofNat 64 offset)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec_li ho,Option.some.injEq,exists_eq_left']
  refine WP.mono hli fun u hu => ?_
  subst u
  have hwr : InRegions (s.write .r11 (BitVec.ofNat 64 offset)).wr
      ((s.write .r11 (BitVec.ofNat 64 offset)).gpr .r16+(s.write .r11 (BitVec.ofNat 64 offset)).gpr .r11) 16 := by
    simpa only [RegUpd.wr_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true] using hw
  refine WP.mono (rawStore_ok v .r16 .r11 _ (by decide) hwr) fun t ht => ?_
  simpa only [RegUpd.mem_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,vpr_write] using ht

def powerMem (m : Mem) (p : Addr) (offset : Nat) (a b : BitVec 128) : Mem :=
  (m.write (p+BitVec.ofNat 64 offset) 16 (swapDwords a)).write
    (p+BitVec.ofNat 64 (offset+16)) 16 (swapDwords b)

theorem powerMem_lo (m : Mem) (p : Addr) (offset : Nat) (a b : BitVec 128)
    (ho : offset+32 ≤ 2^64) :
    swapDwords ((powerMem m p offset a b).read (p+BitVec.ofNat 64 offset) 16)=a := by
  rw [powerMem,Mem.read_write_sep
    (Offset.sep p (Or.inl (Nat.le_refl _)) (by omega) ho) (by decide),
    VG.Proof.VectorCrypto.read_write16,swapDwords_involutive]

theorem powerMem_hi (m : Mem) (p : Addr) (offset : Nat) (a b : BitVec 128) :
    swapDwords ((powerMem m p offset a b).read (p+BitVec.ofNat 64 (offset+16)) 16)=b := by
  rw [powerMem,VG.Proof.VectorCrypto.read_write16,swapDwords_involutive]


theorem powerMem_frame (m : Mem) (p : Addr) (offset start len : Nat) (a b : BitVec 128)
    (hs : start ≤ offset) (ho : offset+32 ≤ start+len) (hl : start+len < 2^64) :
    Frame [⟨p+BitVec.ofNat 64 start,len⟩] m (powerMem m p offset a b) := by
  exact ((Frame.refl _ m).write (List.mem_singleton_self _) _
    (Offset.contains p (d := offset) (n := 16) (e := start) (k := len) hs (by omega) hl)).write
      (List.mem_singleton_self _) _
      (Offset.contains p (d := offset+16) (n := 16) (e := start) (k := len) (by omega) (by omega) hl)

theorem powerMem_other (m : Mem) (p : Addr) (offset q : Nat) (a b : BitVec 128)
    (ho : offset+32 ≤ 2^64) (hq : q+16 ≤ 2^64) (hs : q+16 ≤ offset ∨ offset+32 ≤ q) :
    (powerMem m p offset a b).read (p+BitVec.ofNat 64 q) 16=m.read (p+BitVec.ofNat 64 q) 16 := by
  rw [powerMem,Mem.read_write_sep
    (Offset.sep p (d := q) (n := 16) (e := offset+16) (k := 16) (by omega) hq ho) (by decide),
    Mem.read_write_sep (Offset.sep p (d := q) (n := 16) (e := offset) (k := 16) (by omega) hq (by omega)) (by decide)]

structure PackSaveResult (base : State) (offset : Nat) (s : State) : Prop where
  keep : Keep [.r11] base s
  v : ∀ r, r ∉ [.v9,T,.v8] → s.vpr r=base.vpr r
  mem : s.mem=powerMem base.mem (base.gpr .r16) offset
    (VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair (base.vpr .v12) (base.vpr .v8))
    (VG.Proof.Gcm.PPC64LE.Vpmsum.highPair (base.vpr .v12) (base.vpr .v8))

theorem packSave_ok (offset : Nat) (s : State) (ho : offset+16<2^15)
    (hwl : InRegions s.wr (s.gpr .r16+BitVec.ofNat 64 offset) 16)
    (hwh : InRegions s.wr (s.gpr .r16+BitVec.ofNat 64 (offset+16)) 16) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.packSave offset)) s (PackSaveResult s offset) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.packSave,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (packEven_ok s) fun u ⟨hl,hh,hf⟩ => ?_
  have hwl' : InRegions u.wr (u.gpr .r16+BitVec.ofNat 64 offset) 16 := by
    simpa only [hf.wr,hf.gpr] using hwl
  refine WP.mono (powerSave_ok .v8 offset u (by omega) hwl') fun v hv => ?_
  subst v
  let stored : State := {u.write .r11 (BitVec.ofNat 64 offset) with
    mem := u.mem.write (u.gpr .r16+BitVec.ofNat 64 offset) 16 (swapDwords (u.vpr .v8))}
  have hwh' : InRegions stored.wr (stored.gpr .r16+BitVec.ofNat 64 (offset+16)) 16 := by
    simpa only [stored,RegUpd.wr_write,RegUpd.gpr_write,reduceCtorEq,ite_false,hf.wr,hf.gpr] using hwh
  refine WP.mono (powerSave_ok T (offset+16) _ ho hwh') fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_write,hr,ite_false,hf.gpr]
    · simp only [RegUpd.rd_write,hf.rd]
    · simp only [RegUpd.wr_write,hf.wr]
  · intro r hr
    simpa only [vpr_write] using hf.v r hr
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,vpr_write,hf.mem,hf.gpr,hl,hh,powerMem]


def powerClobbers : List VReg := [.v8,.v9,U,LO,MID,HI,T,.v12]

structure PowerStepResult (base : State) (h : BitVec 128) (j : Nat) (s : State) : Prop where
  keep : Keep [.r11] base s
  v : ∀ r, r ∉ powerClobbers → s.vpr r=base.vpr r
  value : s.vpr .v12=VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (j+1)
  mem : s.mem=if (j+2)%2=0 then
    powerMem base.mem (base.gpr .r16) (Impl.AesGcm.PPC64LE.Blocks.powerOffset j)
      (VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (j+1))
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h j))
      (VG.Proof.Gcm.PPC64LE.Vpmsum.highPair (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (j+1))
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h j))
    else base.mem

theorem powerStep_ok (j : Nat) (h : BitVec 128) (s : State)
    (hv : s.vpr .v12=VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h j)
    (hk : s.vpr .v11=h) (hc : s.vpr .v13=poly++poly) (hz : s.vpr .v0=0)
    (hwl : InRegions s.wr (s.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j)) 16)
    (hwh : InRegions s.wr (s.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j+16)) 16) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.powerStep j)) s (PowerStepResult s h j) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.powerStep,WP.block_append_iff]
  refine WP.mono (powerNext_ok j h s hv hk hc hz) fun u ⟨hu,hod,hf⟩ => ?_
  by_cases he : (j+2)%2=0
  · rw [Impl.AesGcm.PPC64LE.Blocks.powerStore,ite_eq_left he]
    have hwl' : InRegions u.wr (u.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j)) 16 := by
      simpa only [hf.wr,hf.gpr] using hwl
    have hwh' : InRegions u.wr (u.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j+16)) 16 := by
      simpa only [hf.wr,hf.gpr] using hwh
    refine WP.mono (packSave_ok _ u (by unfold Impl.AesGcm.PPC64LE.Blocks.powerOffset; omega) hwl' hwh')
      fun t ht => ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨fun r hr => (ht.keep.gpr hr).trans (congrFun hf.gpr r),
        ht.keep.2.1.trans hf.rd,ht.keep.2.2.trans hf.wr⟩
    · intro r hr
      have hfree : r ∉ [.v9,T,.v8] := by
        simp only [powerClobbers,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr ⊢
        exact ⟨hr.2.1,hr.2.2.2.2.2.2.1,hr.1⟩
      exact (ht.v r hfree).trans (hf.v r hr)
    · exact (ht.v .v12 (by decide)).trans hu
    · rw [ht.mem,hf.mem,hf.gpr,hu,hod,ite_eq_left he,ite_eq_left he]
  · rw [Impl.AesGcm.PPC64LE.Blocks.powerStore,ite_eq_right he]
    exact WP.block_nil ⟨⟨fun r _ => congrFun hf.gpr r,hf.rd,hf.wr⟩,
      hf.v,hu,by rw [ite_eq_right he]; exact hf.mem⟩


def pairOffset (q : Nat) : Nat := 128+32*(3-q)

structure PowerInv (base : State) (h : BitVec 128) (j : Nat) (s : State) : Prop where
  keep : Keep [.r11] base s
  v : ∀ r, r ∉ powerClobbers → s.vpr r=base.vpr r
  value : s.vpr .v12=VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h j
  lo : ∀ q : Fin 4, 2*q.val+1 ≤ j →
    swapDwords (s.mem.read (base.gpr .r16+BitVec.ofNat 64 (pairOffset q)) 16)=
      VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (2*q.val+1))
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (2*q.val))
  hi : ∀ q : Fin 4, 2*q.val+1 ≤ j →
    swapDwords (s.mem.read (base.gpr .r16+BitVec.ofNat 64 (pairOffset q+16)) 16)=
      VG.Proof.Gcm.PPC64LE.Vpmsum.highPair
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (2*q.val+1))
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (2*q.val))
  frame : Frame [⟨base.gpr .r16+128,128⟩] base.mem s.mem

theorem powerOffset_bounds (j : Nat) : 128 ≤ Impl.AesGcm.PPC64LE.Blocks.powerOffset j ∧
    Impl.AesGcm.PPC64LE.Blocks.powerOffset j+32 ≤ 256 := by
  unfold Impl.AesGcm.PPC64LE.Blocks.powerOffset
  omega

theorem powerOffset_eq (q : Fin 4) : Impl.AesGcm.PPC64LE.Blocks.powerOffset (2*q.val)=pairOffset q := by
  unfold Impl.AesGcm.PPC64LE.Blocks.powerOffset pairOffset
  omega

theorem powerOffset_separate (j : Nat) (hj : j<7) (q : Fin 4) (hq : 2*q.val+1 ≤ j)
    (he : (j+2)%2=0) : Impl.AesGcm.PPC64LE.Blocks.powerOffset j+32 ≤ pairOffset q := by
  unfold Impl.AesGcm.PPC64LE.Blocks.powerOffset pairOffset
  omega

theorem powerInv_step {base : State} {h : BitVec 128}
    (hk : base.vpr .v11=h) (hc : base.vpr .v13=poly++poly) (hz : base.vpr .v0=0)
    (writes : ∀ j < 7, InRegions base.wr
      (base.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j)) 16 ∧
      InRegions base.wr (base.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j+16)) 16)
    {j : Nat} (hj : j<7) {s : State} (hs : PowerInv base h j s) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.powerStep j)) s (PowerInv base h (j+1)) := by
  have hks : s.vpr .v11=h := (hs.v .v11 (by decide)).trans hk
  have hcs : s.vpr .v13=poly++poly := (hs.v .v13 (by decide)).trans hc
  have hzs : s.vpr .v0=0 := (hs.v .v0 (by decide)).trans hz
  have hg : s.gpr .r16=base.gpr .r16 := hs.keep.gpr (by decide)
  have hwl : InRegions s.wr (s.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j)) 16 := by
    rw [hs.keep.2.2,hg]; exact (writes j hj).1
  have hwh : InRegions s.wr (s.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j+16)) 16 := by
    rw [hs.keep.2.2,hg]; exact (writes j hj).2
  refine WP.mono (powerStep_ok j h s hs.value hks hcs hzs hwl hwh) fun t ht => ?_
  have hlo : ∀ q : Fin 4, 2*q.val+1 ≤ j+1 →
      swapDwords (t.mem.read (base.gpr .r16+BitVec.ofNat 64 (pairOffset q)) 16)=
        VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (2*q.val+1))
          (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (2*q.val)) := by
    intro q hq
    by_cases heq : 2*q.val=j
    · have he : (j+2)%2=0 := by omega
      rw [ht.mem,ite_eq_left he,hg,← heq,powerOffset_eq]
      exact powerMem_lo _ _ _ _ _ (by unfold pairOffset; omega)
    · have hqold : 2*q.val+1 ≤ j := by omega
      rw [ht.mem]
      by_cases he : (j+2)%2=0
      · rw [ite_eq_left he,hg,powerMem_other _ _ _ _ _ _ (by have := powerOffset_bounds j; omega)
          (by unfold pairOffset; omega) (Or.inr (powerOffset_separate j hj q hqold he))]
        exact hs.lo q hqold
      · rw [ite_eq_right he]; exact hs.lo q hqold
  have hhi : ∀ q : Fin 4, 2*q.val+1 ≤ j+1 →
      swapDwords (t.mem.read (base.gpr .r16+BitVec.ofNat 64 (pairOffset q+16)) 16)=
        VG.Proof.Gcm.PPC64LE.Vpmsum.highPair (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (2*q.val+1))
          (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (2*q.val)) := by
    intro q hq
    by_cases heq : 2*q.val=j
    · have he : (j+2)%2=0 := by omega
      rw [ht.mem,ite_eq_left he,hg,← heq,powerOffset_eq]
      exact powerMem_hi _ _ _ _ _
    · have hqold : 2*q.val+1 ≤ j := by omega
      rw [ht.mem]
      by_cases he : (j+2)%2=0
      · rw [ite_eq_left he,hg,powerMem_other _ _ _ _ _ _ (by have := powerOffset_bounds j; omega)
          (by unfold pairOffset; omega) (Or.inr (by have := powerOffset_separate j hj q hqold he; omega))]
        exact hs.hi q hqold
      · rw [ite_eq_right he]; exact hs.hi q hqold
  refine ⟨(hs.keep.trans ht.keep).mono (by simp),fun r hr => (ht.v r hr).trans (hs.v r hr),
    ht.value,hlo,hhi,?_⟩
  rw [ht.mem]
  by_cases he : (j+2)%2=0
  · rw [ite_eq_left he,hg]
    exact hs.frame.trans (powerMem_frame _ _ _ 128 128 _ _ (powerOffset_bounds j).1
      (powerOffset_bounds j).2 (by decide))
  · rw [ite_eq_right he]; exact hs.frame


theorem foldSetup_ok (base : State) (h : BitVec 128)
    (hk : base.vpr .v11=h) (hc : base.vpr .v13=poly++poly) (hz : base.vpr .v0=0)
    (writes : ∀ j < 7, InRegions base.wr
      (base.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j)) 16 ∧
      InRegions base.wr (base.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j+16)) 16) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.foldSetup) base (PowerInv base h 7) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.foldSetup,WP.block_append_iff]
  refine WP.mono (vector_step (.vop (.logic .or .v12 .v11 .v11)) .v12 _ base
    (exec_copyVector .v12 .v11 base)) fun u ⟨hu,hf⟩ => ?_
  have hk' : u.vpr .v11=h := (hf.v .v11 (by decide)).trans hk
  have hc' : u.vpr .v13=poly++poly := (hf.v .v13 (by decide)).trans hc
  have hz' : u.vpr .v0=0 := (hf.v .v0 (by decide)).trans hz
  have wrs : ∀ j < 7, InRegions u.wr
      (u.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j)) 16 ∧
      InRegions u.wr (u.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j+16)) 16 := by
    intro j hj
    simpa only [hf.wr,hf.gpr] using writes j hj
  have hi : PowerInv u h 0 u := ⟨Keep.refl _ _,fun _ _ => rfl,hu.trans hk,
    fun q hq => False.elim (by omega),fun q hq => False.elim (by omega),Frame.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (PowerInv u h)
    (fun j t hj ht => powerInv_step hk' hc' hz' wrs hj ht) 7 (Nat.le_refl _) u hi) fun t ht => ?_
  refine ⟨?_, ?_, ht.value, ?_, ?_, ?_⟩
  · exact ⟨fun r hr => (ht.keep.gpr hr).trans (congrFun hf.gpr r),
      ht.keep.2.1.trans hf.rd,ht.keep.2.2.trans hf.wr⟩
  · intro r hr
    have hr' : r ∉ [.v12] := by
      intro he
      rw [List.mem_singleton] at he
      apply hr
      rw [he]; decide
    exact (ht.v r hr).trans (hf.v r hr')
  · intro q hq
    simpa only [hf.gpr] using ht.lo q hq
  · intro q hq
    simpa only [hf.gpr] using ht.hi q hq
  · simpa only [hf.gpr,hf.mem] using ht.frame

def PowersAt (m : Mem) (p : Addr) (h : BitVec 128) : Prop :=
  ∀ j < 4,
    swapDwords (m.read (p+BitVec.ofNat 64 (128+32*j)) 16)=
      VG.Proof.Gcm.PPC64LE.Vpmsum.lowPair (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (7-2*j))
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (6-2*j)) ∧
    swapDwords (m.read (p+BitVec.ofNat 64 (144+32*j)) 16)=
      VG.Proof.Gcm.PPC64LE.Vpmsum.highPair (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (7-2*j))
        (VG.Proof.Gcm.PPC64LE.Vpmsum.keyValue h (6-2*j))

theorem PowerInv.ready {base s : State} {h : BitVec 128} (hs : PowerInv base h 7 s) :
    PowersAt s.mem (base.gpr .r16) h := by
  intro j hj
  let q : Fin 4 := ⟨3-j,by omega⟩
  have hl := hs.lo q (by dsimp only [q]; omega)
  have hh := hs.hi q (by dsimp only [q]; omega)
  have ho : pairOffset q=128+32*j := by
    change 128+32*(3-(3-j))=128+32*j
    omega
  have hk : 2*q.val+1=7-2*j := by dsimp only [q]; omega
  have hk' : 2*q.val=6-2*j := by dsimp only [q]; omega
  rw [ho,hk,hk'] at hl hh
  refine ⟨hl, ?_⟩
  simpa only [show 128+32*j+16=144+32*j by omega] using hh


theorem hashInit_ok (base : State) (h : BitVec 128)
    (hz : base.vpr .v0=0) (h0 : base.gpr .r0=0)
    (hm : base.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask)
    (hr : InRegions (base.rd++base.wr) (base.gpr .r8) 16)
    (hh : rev128 (base.mem.read (base.gpr .r8) 16)=h) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.hashInit) base fun t =>
      t.vpr .v11=VG.Proof.Gcm.PPC64LE.Vpmsum.adjustedKey h ∧ t.vpr .v13=poly++poly ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local [.r11,.r12] [.v13,.v1,.v11,.v9,U,LO,MID,HI,T] base t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.hashInit]
  repeat rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.setMask_ok .v13 (poly++poly) base (by decide) (by decide) hz)
    fun s ⟨hp,hf⟩ => ?_
  have hz' : s.vpr .v0=0 := (hf.v .v0 (by decide)).trans hz
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.setMask_ok .v11 (VG.Proof.Gcm.Clmul.xInv2) s
    (by decide) (by decide) hz') fun u ⟨hk,hg⟩ => ?_
  have he := hf.trans hg
  have h0' : u.gpr .r0=0 := (he.keep.gpr (by decide)).trans h0
  have hm' : u.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask := (he.v .v19 (by decide)).trans hm
  have hr' : InRegions (u.rd++u.wr) (u.gpr .r8) 16 := by
    rw [he.keep.2.1,he.keep.2.2,he.keep.gpr (by decide)]; exact hr
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.load_ok .v9 .r8 u (by decide) (by decide) h0' hm' hr')
    fun v ⟨hv,hi⟩ => ?_
  have h9 : v.vpr .v9=h := by rw [hv,he.mem,he.keep.gpr (by decide)]; exact hh
  refine WP.mono (vector_step (.vop (.sldoi .v9 .v9 .v9 8)) .v9 _ v
    (VG.Proof.Gcm.PPC64LE.Vpmsum.exec_shift8 .v9 .v9 .v9 v)) fun w ⟨hw,hj⟩ => ?_
  have hw9 : w.vpr .v9=VG.Proof.Gcm.Clmul.ext8 h h := by
    rw [hw,VG.Proof.Gcm.PPC64LE.Vpmsum.half_self,h9]
  have hke : w.vpr .v11=VG.Proof.Gcm.Clmul.xInv2 :=
    (hj.v .v11 (by decide)).trans ((hi.v .v11 (by decide)).trans hk)
  have hpe : w.vpr .v13=poly++poly :=
    (hj.v .v13 (by decide)).trans ((hi.v .v13 (by decide)).trans ((hg.v .v13 (by decide)).trans hp))
  have hze : w.vpr .v0=0 :=
    (hj.v .v0 (by decide)).trans ((hi.v .v0 (by decide)).trans ((hg.v .v0 (by decide)).trans hz'))
  refine WP.mono (mul_ok .v11 .v9 .v11 w (by decide) (by decide) hpe hze) fun z ⟨hzv,hl⟩ => ?_
  refine WP.mono (vector_step (.vop (.sldoi .v11 .v11 .v11 8)) .v11 _ z
    (VG.Proof.Gcm.PPC64LE.Vpmsum.exec_shift8 .v11 .v11 .v11 z)) fun t ⟨ht,hn⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht,VG.Proof.Gcm.PPC64LE.Vpmsum.half_self,hzv,hw9,hke]
    rfl
  · exact (hn.v .v13 (by decide)).trans ((hl.v .v13 (by decide)).trans hpe)
  · have hlocal := (((he.trans (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hi)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hj)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hl)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hn)
    exact hlocal.weaken (by simp) (by simp [or_left_comm,or_comm])


structure EntryPtrsResult (base s : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local [.r16,.r14,.r15] [] base s
  table : s.gpr .r16=base.gpr .r10+128
  y : s.gpr .r14=base.gpr .r9
  offset : s.gpr .r15=112

theorem entryPtrs_ok (base : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entryPtrs) base (EntryPtrsResult base) := by
  have he : WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entryPtrs) base
      (· = (((base.write .r16 (base.gpr .r10)).write .r16 (base.gpr .r10+128)).write
        .r14 (base.gpr .r9)).write .r15 112) := by
    apply WP.of_runBlock
    simp only [Impl.AesGcm.PPC64LE.Blocks.entryPtrs,Impl.Aes.PPC64LE.Crypto.mov,
      runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
      exec_addi (n := .r16) (imm := 128) (by decide) (by decide),
      exec_li (imm := 112) (by decide),RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false,
      Option.some.injEq,exists_eq_left']
    rfl
  refine WP.mono he fun s hs => ?_
  subst s
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hl := (((VG.Proof.Aes.PPC64LE.Crypto.Local.write base .r16 (base.gpr .r10)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r16 (base.gpr .r10+128))).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r14 (base.gpr .r9))).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r15 112)
    exact hl.weaken (by simp [or_left_comm]) (by simp)
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
  · exact RegUpd.gpr_write_self ..

structure EntryConstsResult (base s : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local [.r20,.r24,.r18] [] base s
  one : s.gpr .r20=16
  cache : s.gpr .r24=base.gpr .r16+256
  offset : s.gpr .r18=96

theorem entryConsts_ok (base : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entryConsts) base (EntryConstsResult base) := by
  have he : WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entryConsts) base
      (· = ((base.write .r20 16).write .r24 (base.gpr .r16+256)).write .r18 96) := by
    apply WP.of_runBlock
    simp only [Impl.AesGcm.PPC64LE.Blocks.entryConsts,runBlock_cons,runStep_some,runBlock_nil,
      exec_li (imm := 16) (by decide),exec_addi (n := .r16) (imm := 256) (by decide) (by decide),
      exec_li (imm := 96) (by decide),RegUpd.gpr_write,reduceCtorEq,ite_false,
      Option.some.injEq,exists_eq_left']
    rfl
  refine WP.mono he fun s hs => ?_
  subst s
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hl := ((VG.Proof.Aes.PPC64LE.Crypto.Local.write base .r20 16).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r24 (base.gpr .r16+256))).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r18 96)
    exact hl.weaken (by simp) (by simp)
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
  · exact RegUpd.gpr_write_self ..


theorem saveCore_ok (s : State)
    (writes : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved,
      InRegions s.wr (s.gpr .r10+BitVec.ofNat 64 p.2) 8) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.saved.map (fun (r,o) => .store .d r .r10 o))) s
      (· = {s with mem := Spill.saveMem s.mem (s.gpr .r10) s.gpr Impl.AesGcm.PPC64LE.Blocks.saved}) := by
  change WP isa (.block (Spill.saveCode .r10 Impl.AesGcm.PPC64LE.Blocks.saved)) s _
  rw [← List.append_nil (Spill.saveCode .r10 Impl.AesGcm.PPC64LE.Blocks.saved)]
  exact Spill.save_ok (by decide)
    (show ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, p.2%8=0 ∧ p.2<32768 from by decide)
    writes (WP.block_nil rfl)

theorem counterWord_ok (base : State)
    (hr : InRegions (base.rd++base.wr) (base.gpr .r5+12#64) 4) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.counterWord) base fun s =>
      (s.gpr .r8).setWidth 32=(Spec.Gcm.blockAt base.mem (base.gpr .r5)).extractLsb' 0 32 ∧
      s.gpr .r11=12#64 ∧ VG.Proof.Aes.PPC64LE.Crypto.Local [.r11,.r8] [] base s := by
  have hr' : InRegions ((base.write .r11 12#64).rd++(base.write .r11 12#64).wr)
      ((base.write .r11 12#64).gpr .r5+(base.write .r11 12#64).gpr .r11) 4 := by
    simpa only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false] using hr
  have he : WP isa (.block Impl.AesGcm.PPC64LE.Blocks.counterWord) base
      (· = (base.write .r11 12#64).write .r8
        ((rev32 (base.mem.readW (base.gpr .r5+12#64) 32)).setWidth 64)) := by
    apply WP.of_runBlock
    simp only [Impl.AesGcm.PPC64LE.Blocks.counterWord,runBlock_cons,runStep_some,runBlock_nil,
      exec_li (imm := 12) (by decide),exec_loadRev_w (s := base.write .r11 12#64) (a := .r5) (b := .r11) (by decide) hr',
      RegUpd.mem_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,
      Option.some.injEq,exists_eq_left']
  refine WP.mono he fun s hs => ?_
  subst s
  refine ⟨?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write_self,BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq,
      VG.Proof.Aes.PPC64LE.Crypto.icb_lo]
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
  · exact ((VG.Proof.Aes.PPC64LE.Crypto.Local.write base .r11 12#64).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r8
        ((rev32 (base.mem.readW (base.gpr .r5+12#64) 32)).setWidth 64))).weaken (by simp) (by simp)


def coreKey (s : State) : Region := ⟨s.gpr .r3,256⟩
def coreCounter (s : State) : Region := ⟨s.gpr .r5,16⟩
def coreY (s : State) : Region := ⟨s.gpr .r9,16⟩
def coreData (s : State) (n : Nat) : Region := ⟨s.gpr .r6,16*n⟩
def coreWork (s : State) : Region := ⟨s.gpr .r10,2048⟩

structure CoreLayout (base : State) (n : Nat) : Prop where
  reads : Covers [coreKey base] (base.rd++base.wr)
  writes : Covers [coreCounter base,coreY base,coreData base n,coreWork base] base.wr
  scratch : ∀ r ∈ [coreKey base,coreCounter base,coreY base,coreData base n], r.Disjoint (coreWork base)
  data : ∀ r ∈ [coreKey base,coreCounter base,coreY base], r.Disjoint (coreData base n)
  counterKey : (coreKey base).Disjoint (coreCounter base)
  yKey : (coreKey base).Disjoint (coreY base)
  counterY : (coreCounter base).Disjoint (coreY base)
  size : 16*n ≤ 2^64

theorem CoreLayout.work_write {base : State} {n offset len : Nat} (hs : CoreLayout base n)
    (ho : offset+len ≤ 2048) : InRegions base.wr (base.gpr .r10+BitVec.ofNat 64 offset) len := by
  exact hs.writes _ _ ⟨coreWork base,by simp,Offset.contains_base _ ho (by omega)⟩

theorem CoreLayout.key_read {base : State} {n offset len : Nat} (hs : CoreLayout base n)
    (ho : offset+len ≤ 256) : InRegions (base.rd++base.wr) (base.gpr .r3+BitVec.ofNat 64 offset) len := by
  exact hs.reads _ _ ⟨coreKey base,List.mem_singleton_self _,Offset.contains_base _ ho (by omega)⟩

theorem CoreLayout.input_read {base : State} {n : Nat} (hs : CoreLayout base n)
    {m m' : Mem} (hf : Frame [coreWork base] m m') {r : Region}
    (hr : r ∈ [coreKey base,coreCounter base,coreY base,coreData base n])
    {p : Addr} {len : Nat} (hp : r.Contains p len) (hl : len<2^64) :
    m'.read p len=m.read p len := by
  exact hf.read hp (by simpa only [List.mem_singleton,forall_eq] using hs.scratch r hr) hl

theorem CoreLayout.key_block {base : State} {n offset : Nat} (hs : CoreLayout base n)
    {m m' : Mem} (hf : Frame [coreWork base] m m') (ho : offset+16 ≤ 256) :
    Spec.Gcm.blockAt m' (base.gpr .r3+BitVec.ofNat 64 offset)=
      Spec.Gcm.blockAt m (base.gpr .r3+BitVec.ofNat 64 offset) := by
  rw [← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt]
  rw [hs.input_read (r := coreKey base) hf (by simp) (Offset.contains_base _ ho (by omega)) (by decide)]

theorem CoreLayout.saved_frame {base : State} {n : Nat} (_hs : CoreLayout base n) :
    Frame [coreWork base] base.mem
      (Spill.saveMem base.mem (base.gpr .r10) base.gpr Impl.AesGcm.PPC64LE.Blocks.saved) := by
  simpa only [coreWork,BitVec.add_zero] using (Spill.saveMem_frame (lo := 0) (n := 2048)
    (show ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, 0 ≤ p.2 ∧ p.2+8 ≤ 2048 from by decide)
    (by decide) base.mem (base.gpr .r10) base.gpr)


structure InitOneResult (base s : State) : Prop where
  keep : Keep [.r11,.r12] base s
  v : ∀ r, r ∉ [U,.v1] → s.vpr r=base.vpr r
  value : s.vpr U=1
  mem : s.mem=base.mem.write (base.gpr .r16+base.gpr .r20) 16 (swapDwords 1)

theorem initOne_ok (base : State) (hz : base.vpr .v0=0)
    (hw : InRegions base.wr (base.gpr .r16+base.gpr .r20) 16) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.initOne) base (InitOneResult base) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.initOne,WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.setMask_ok U 1 base (by decide) (by decide) hz)
    fun s ⟨hs,hf⟩ => ?_
  have hw' : InRegions s.wr (s.gpr .r16+s.gpr .r20) 16 := by
    rw [hf.keep.2.2,hf.keep.gpr (by decide),hf.keep.gpr (by decide)]; exact hw
  refine WP.mono (rawStore_ok U .r16 .r20 s (by decide) hw') fun t ht => ?_
  subst t
  refine ⟨hf.keep,hf.v,hs,?_⟩
  change s.mem.write (s.gpr .r16+s.gpr .r20) 16 (swapDwords (s.vpr U))=_
  rw [hf.mem,hf.keep.gpr (by decide),hf.keep.gpr (by decide),hs]


structure EntryConfigResult (base s : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local [.r16,.r14,.r15,.r0,.r11,.r12,.r20,.r24,.r18]
    [.v0,.v1,.v19] base s
  table : s.gpr .r16=base.gpr .r10+128
  y : s.gpr .r14=base.gpr .r9
  counterOffset : s.gpr .r15=112
  oneOffset : s.gpr .r20=16
  cache : s.gpr .r24=base.gpr .r10+384
  dataOffset : s.gpr .r18=96
  zero : s.gpr .r0=0
  vzero : s.vpr .v0=0
  mask : s.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask

theorem entryConfig_ok (base : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entryConfig) base (EntryConfigResult base) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.entryConfig,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (entryPtrs_ok base) fun s hs => ?_
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.setup_ok s) fun u ⟨h0,hm,hz,hf⟩ => ?_
  refine WP.mono (entryConsts_ok u) fun t ht => ?_
  refine ⟨?_, ?_, ?_, ?_, ht.one, ?_, ht.offset, ?_, ?_, ?_⟩
  · exact ((hs.effects.trans hf).trans ht.effects).weaken (by simp) (by simp)
  · rw [ht.effects.keep.gpr (by decide),hf.keep.gpr (by decide)]
    exact hs.table
  · rw [ht.effects.keep.gpr (by decide),hf.keep.gpr (by decide)]
    exact hs.y
  · rw [ht.effects.keep.gpr (by decide),hf.keep.gpr (by decide)]
    exact hs.offset
  · rw [ht.cache,hf.keep.gpr (by decide),hs.table]
    change base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 256=_
    rw [Offset.add_add]
    rfl
  · exact (ht.effects.keep.gpr (by decide)).trans h0
  · exact (ht.effects.v .v0 (by simp)).trans hz
  · exact (ht.effects.v .v19 (by simp)).trans hm


structure EntrySecretsResult (base : State) (h : BitVec 128) (s : State) : Prop where
  effects : VG.Proof.Aes.PPC64LE.Crypto.Local [.r11,.r12,.r8,.r9]
    [.v13,.v1,.v11,.v9,U,LO,MID,HI,T,.v10] base s
  key : s.vpr .v11=VG.Proof.Gcm.PPC64LE.Vpmsum.adjustedKey h
  poly : s.vpr .v13=poly++poly
  y : s.vpr .v10=rev128 (base.mem.read (base.gpr .r14) 16)
  word : (s.gpr .r8).setWidth 32=(Spec.Gcm.blockAt base.mem (base.gpr .r5)).extractLsb' 0 32
  source : s.gpr .r9=base.gpr .r3

theorem entrySecrets_ok (base : State) (h : BitVec 128)
    (hz : base.vpr .v0=0) (h0 : base.gpr .r0=0)
    (hm : base.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask)
    (hr : InRegions (base.rd++base.wr) (base.gpr .r8) 16)
    (hh : rev128 (base.mem.read (base.gpr .r8) 16)=h)
    (hy : InRegions (base.rd++base.wr) (base.gpr .r14) 16)
    (hcb : InRegions (base.rd++base.wr) (base.gpr .r5+12#64) 4) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entrySecrets) base (EntrySecretsResult base h) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.entrySecrets,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (hashInit_ok base h hz h0 hm hr hh) fun s ⟨hk,hp,hf⟩ => ?_
  have h0s : s.gpr .r0=0 := (hf.keep.gpr (by decide)).trans h0
  have hms : s.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask := (hf.v .v19 (by decide)).trans hm
  have hys : InRegions (s.rd++s.wr) (s.gpr .r14) 16 := by
    rw [hf.keep.2.1,hf.keep.2.2,hf.keep.gpr (by decide)]; exact hy
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.load_ok .v10 .r14 s (by decide) (by decide) h0s hms hys)
    fun u ⟨hu,hg⟩ => ?_
  have hcb' : InRegions (u.rd++u.wr) (u.gpr .r5+12#64) 4 := by
    rw [hg.rd,hg.wr,hg.gpr,hf.keep.2.1,hf.keep.2.2,hf.keep.gpr (by decide)]; exact hcb
  refine WP.mono (counterWord_ok u hcb') fun v ⟨hv,_,hi⟩ => ?_
  have hcopy : WP isa (.block ([Impl.Aes.PPC64LE.Crypto.mov .r9 .r3] : List Instr)) v
      (· = v.write .r9 (v.gpr .r3)) := by
    apply WP.of_runBlock
    simp only [Impl.Aes.PPC64LE.Crypto.mov,runBlock_cons,runStep_some,runBlock_nil,exec_logic,
      BitVec.or_self,Option.some.injEq,exists_eq_left']
  refine WP.mono hcopy fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he := ((hf.trans (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hg)).trans hi).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.write v .r9 (v.gpr .r3))
    exact he.weaken (by simp [or_left_comm]) (by simp)
  · simpa only [vpr_write,hi.v .v11 (by simp),hg.v .v11 (by decide)] using hk
  · simpa only [vpr_write,hi.v .v13 (by simp),hg.v .v13 (by decide)] using hp
  · simpa only [vpr_write,hi.v .v10 (by simp),hf.mem,hf.keep.gpr (r := .r14) (by decide)] using hu
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false,hg.mem,hg.gpr,hf.mem,hf.keep.gpr (r := .r5) (by decide)] using hv
  · rw [RegUpd.gpr_write_self,hi.keep.gpr (by decide),hg.gpr,hf.keep.gpr (by decide)]


def coreBody (base : State) : Region := ⟨base.gpr .r10+128,1920⟩

theorem coreBody_sub (base : State) : Region.Sub (coreBody base) (coreWork base) :=
  Offset.sub_base _ (by decide)

theorem coreBody_frame {base : State} {m m' : Mem} (hf : Frame [coreBody base] m m') :
    Frame [coreWork base] m m' := by
  exact hf.sub (fun r hr => by
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨coreWork base,List.mem_singleton_self _,coreBody_sub base⟩)

theorem saved_after_body (base : State) {m : Mem}
    (hf : Frame [coreBody base]
      (Spill.saveMem base.mem (base.gpr .r10) base.gpr Impl.AesGcm.PPC64LE.Blocks.saved) m) :
    Spill.Saved (base.gpr .r10) base.gpr Impl.AesGcm.PPC64LE.Blocks.saved m := by
  have hs := Spill.saveMem_saved (show Spill.Fits Impl.AesGcm.PPC64LE.Blocks.saved from by decide)
    base.mem (base.gpr .r10) base.gpr
  refine hs.frame hf fun p hp r hr => ?_
  rw [List.mem_singleton] at hr
  subst r
  have hb : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, p.2+8 ≤ 128 := by decide
  exact Offset.disjoint _ (Or.inl (hb p hp)) (by have := hb p hp; omega) (by decide)

theorem CoreLayout.input_block {base : State} {n : Nat} (hs : CoreLayout base n)
    {m m' : Mem} (hf : Frame [coreWork base] m m') {r : Region}
    (hr : r ∈ [coreKey base,coreCounter base,coreY base,coreData base n])
    {p : Addr} (hp : r.Contains p 16) : Spec.Gcm.blockAt m' p=Spec.Gcm.blockAt m p := by
  rw [← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,
    hs.input_read hf hr hp (by decide)]


theorem entryFinish_ok (base : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entryFinish) base
      (· = (base.write .r11 (base.gpr .r24)).write .r12 (base.gpr .r4+1)) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.entryFinish,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    exec_addi (n := .r4) (imm := 1) (by decide) (by decide),RegUpd.gpr_write,
    reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl


def entryGprs : List Reg := [.r16,.r14,.r15,.r0,.r11,.r12,.r20,.r24,.r18,.r8,.r9]

def coreSavedMem (base : State) : Mem :=
  Spill.saveMem base.mem (base.gpr .r10) base.gpr Impl.AesGcm.PPC64LE.Blocks.saved

structure PrePowers (base s : State) : Prop where
  keep : Keep entryGprs base s
  frame : Frame [coreBody base] (coreSavedMem base) s.mem
  table : s.gpr .r16=base.gpr .r10+128
  yPtr : s.gpr .r14=base.gpr .r9
  counterOffset : s.gpr .r15=112
  oneOffset : s.gpr .r20=16
  dataOffset : s.gpr .r18=96
  cache : s.gpr .r24=base.gpr .r10+384
  source : s.gpr .r9=base.gpr .r3
  zero : s.gpr .r0=0
  vzero : s.vpr .v0=0
  mask : s.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask
  poly : s.vpr .v13=poly++poly
  key : s.vpr .v11=VG.Proof.Gcm.PPC64LE.Vpmsum.adjustedKey (Spec.Gcm.ctxH base.mem (base.gpr .r3))
  y : s.vpr .v10=Spec.Gcm.blockAt base.mem (base.gpr .r9)
  word : (s.gpr .r8).setWidth 32=(Spec.Gcm.blockAt base.mem (base.gpr .r5)).extractLsb' 0 32
  one : swapDwords (s.mem.read (base.gpr .r10+144) 16)=1

theorem PrePowers.advance {base s t : State} (hs : PrePowers base s)
    (hk : Keep [.r11,.r12] s t)
    (hv : ∀ r ∈ [.v0,.v19,.v13,.v11,.v10], t.vpr r=s.vpr r)
    (hf : Frame [coreBody base] s.mem t.mem)
    (ho : t.mem.read (base.gpr .r10+144) 16=s.mem.read (base.gpr .r10+144) 16) :
    PrePowers base t := by
  refine ⟨(hs.keep.trans hk).mono (by simp [entryGprs]),hs.frame.trans hf,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hk.gpr (by decide)).trans hs.table
  · exact (hk.gpr (by decide)).trans hs.yPtr
  · exact (hk.gpr (by decide)).trans hs.counterOffset
  · exact (hk.gpr (by decide)).trans hs.oneOffset
  · exact (hk.gpr (by decide)).trans hs.dataOffset
  · exact (hk.gpr (by decide)).trans hs.cache
  · exact (hk.gpr (by decide)).trans hs.source
  · exact (hk.gpr (by decide)).trans hs.zero
  · exact (hv .v0 (by simp)).trans hs.vzero
  · exact (hv .v19 (by simp)).trans hs.mask
  · exact (hv .v13 (by simp)).trans hs.poly
  · exact (hv .v11 (by simp)).trans hs.key
  · exact (hv .v10 (by simp)).trans hs.y
  · rw [hk.gpr (by decide)]; exact hs.word
  · rw [ho]; exact hs.one


theorem entryPrep_ok (base : State) (n : Nat) (lay : CoreLayout base n)
    (hH : base.gpr .r8=base.gpr .r3+240#64) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entryPrep) base (PrePowers base) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.entryPrep,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  have hw : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved,
      InRegions base.wr (base.gpr .r10+BitVec.ofNat 64 p.2) 8 := by
    intro p hp
    have hb : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, p.2+8 ≤ 2048 := by decide
    exact lay.work_write (hb p hp)
  refine WP.mono (saveCore_ok base hw) fun initial hinitial => ?_
  subst initial
  refine WP.mono (entryConfig_ok {base with mem := coreSavedMem base}) fun cfg hc => ?_
  have hck : Keep [.r16,.r14,.r15,.r0,.r11,.r12,.r20,.r24,.r18] base cfg := hc.effects.keep
  have hcm : cfg.mem=coreSavedMem base := hc.effects.mem
  have hcw : InRegions cfg.wr (cfg.gpr .r16+cfg.gpr .r20) 16 := by
    rw [hck.2.2,hc.table,hc.oneOffset]
    change InRegions base.wr (base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 16) 16
    rw [Offset.add_add]
    exact lay.work_write (by decide)
  refine WP.mono (initOne_ok cfg hc.vzero hcw) fun one ho => ?_
  have hg : Keep ([.r16,.r14,.r15,.r0,.r11,.r12,.r20,.r24,.r18]++[.r11,.r12]) base one :=
    hck.trans ho.keep
  have hom : one.mem=(coreSavedMem base).write (base.gpr .r10+144) 16 (swapDwords 1) := by
    rw [ho.mem,hcm,hc.table,hc.oneOffset]
    change (coreSavedMem base).write (base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 16) 16 _=_
    rw [Offset.add_add]
    rfl
  have hof : Frame [coreBody base] (coreSavedMem base) one.mem := by
    rw [hom]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _
      (Offset.contains _ (d := 144) (n := 16) (e := 128) (k := 1920) (by decide) (by decide) (by decide))
  have hframe : Frame [coreWork base] base.mem one.mem :=
    lay.saved_frame.trans (coreBody_frame hof)
  have hreadwr : Covers base.wr (base.rd++base.wr) := by
    intro p len hh
    obtain ⟨r,hr,hp⟩ := hh
    exact ⟨r,List.mem_append_right _ hr,hp⟩
  have hhr : InRegions (one.rd++one.wr) (one.gpr .r8) 16 := by
    rw [hg.2.1,hg.2.2,hg.gpr (by decide),hH]
    exact lay.key_read (by decide)
  have hhv : rev128 (one.mem.read (one.gpr .r8) 16)=Spec.Gcm.ctxH base.mem (base.gpr .r3) := by
    rw [hg.gpr (by decide),hH]
    rw [lay.input_read (r := coreKey base) hframe (by simp)
      (Offset.contains_base _ (d := 240) (n := 16) (k := 256) (by decide) (by decide)) (by decide)]
    exact VG.Proof.Aes.PPC64LE.Crypto.read_blockAt _ _
  have hyo : one.gpr .r14=base.gpr .r9 := (ho.keep.gpr (by decide)).trans hc.y
  have hyr : InRegions (one.rd++one.wr) (one.gpr .r14) 16 := by
    rw [hg.2.1,hg.2.2,hyo]
    exact hreadwr _ _ (lay.writes _ _ ⟨coreY base,by simp,Region.contains_self _ _⟩)
  have hcr : InRegions (one.rd++one.wr) (one.gpr .r5+12#64) 4 := by
    rw [hg.2.1,hg.2.2,hg.gpr (by decide)]
    exact hreadwr _ _ (lay.writes _ _ ⟨coreCounter base,by simp,
      Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide)⟩)
  have hz1 : one.vpr .v0=0 := (ho.v .v0 (by decide)).trans hc.vzero
  have h01 : one.gpr .r0=0 := (ho.keep.gpr (by decide)).trans hc.zero
  have hm1 : one.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask := (ho.v .v19 (by decide)).trans hc.mask
  refine WP.mono (entrySecrets_ok one _ hz1 h01 hm1 hhr hhv hyr hcr) fun secret hs => ?_
  refine ⟨(hg.trans hs.effects.keep).mono (by simp [entryGprs]),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hs.poly,hs.key,?_,?_,?_⟩
  · simpa only [hs.effects.mem] using hof
  · exact (hs.effects.keep.gpr (by decide)).trans ((ho.keep.gpr (by decide)).trans hc.table)
  · exact (hs.effects.keep.gpr (by decide)).trans hyo
  · exact (hs.effects.keep.gpr (by decide)).trans ((ho.keep.gpr (by decide)).trans hc.counterOffset)
  · exact (hs.effects.keep.gpr (by decide)).trans ((ho.keep.gpr (by decide)).trans hc.oneOffset)
  · exact (hs.effects.keep.gpr (by decide)).trans ((ho.keep.gpr (by decide)).trans hc.dataOffset)
  · exact (hs.effects.keep.gpr (by decide)).trans ((ho.keep.gpr (by decide)).trans hc.cache)
  · exact hs.source.trans (hg.gpr (by decide))
  · exact (hs.effects.keep.gpr (by decide)).trans h01
  · exact (hs.effects.v .v0 (by decide)).trans hz1
  · exact (hs.effects.v .v19 (by decide)).trans hm1
  · rw [hs.y,hyo,lay.input_read (r := coreY base) hframe (by simp) (Region.contains_self _ _) (by decide)]
    exact VG.Proof.Aes.PPC64LE.Crypto.read_blockAt _ _
  · have hb : Spec.Gcm.blockAt one.mem (one.gpr .r5)=Spec.Gcm.blockAt base.mem (base.gpr .r5) := by
      rw [hg.gpr (by decide)]
      exact lay.input_block (r := coreCounter base) hframe (by simp) (Region.contains_self _ _)
    simpa only [hb] using hs.word
  · rw [hs.effects.mem,hom,VG.Proof.VectorCrypto.read_write16,swapDwords_involutive]


structure EntryResult (base s : State) : Prop where
  pre : PrePowers base s
  dest : s.gpr .r11=base.gpr .r10+384
  count : s.gpr .r12=base.gpr .r4+1
  powers : PowersAt s.mem (base.gpr .r10+128)
    (VG.Proof.Gcm.PPC64LE.Vpmsum.adjustedKey (Spec.Gcm.ctxH base.mem (base.gpr .r3)))

theorem entry_ok (base : State) (n : Nat) (lay : CoreLayout base n)
    (hH : base.gpr .r8=base.gpr .r3+240#64) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.entry) base (EntryResult base) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.entry,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (entryPrep_ok base n lay hH) fun prep hs => ?_
  have writable : ∀ off, off+16 ≤ 512 → InRegions prep.wr (prep.gpr .r16+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hs.keep.2.2,hs.table]
    change InRegions base.wr (base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 off) 16
    rw [Offset.add_add]
    exact lay.work_write (by omega)
  have writes : ∀ j < 7, InRegions prep.wr
      (prep.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j)) 16 ∧
      InRegions prep.wr (prep.gpr .r16+BitVec.ofNat 64 (Impl.AesGcm.PPC64LE.Blocks.powerOffset j+16)) 16 := by
    intro j _
    have hb := powerOffset_bounds j
    exact ⟨writable _ (by omega),writable _ (by omega)⟩
  refine WP.mono (foldSetup_ok prep _ hs.key hs.poly hs.vzero writes) fun pow hp => ?_
  have hbody : Frame [coreBody base] prep.mem pow.mem := hp.frame.sub (fun r hr => by
    rw [List.mem_singleton] at hr
    subst r
    refine ⟨coreBody base,List.mem_singleton_self _,?_⟩
    change Region.Sub ⟨prep.gpr .r16+128,128⟩ ⟨base.gpr .r10+128,1920⟩
    rw [hs.table]
    exact Offset.sub_base _ (by decide))
  have haddr : base.gpr .r10+144=prep.gpr .r16+16 := by
    rw [hs.table]
    change base.gpr .r10+BitVec.ofNat 64 144=base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 16
    rw [Offset.add_add]
  have hone : pow.mem.read (base.gpr .r10+144) 16=prep.mem.read (base.gpr .r10+144) 16 := by
    rw [haddr]
    exact hp.frame.read (Region.contains_self _ _) (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint _ (d := 16) (n := 16) (e := 128) (k := 128)
        (Or.inl (by decide)) (by decide) (by decide)) (by decide)
  have hcrit : ∀ r ∈ [.v0,.v19,.v13,.v11,.v10], pow.vpr r=prep.vpr r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hp.v _ (by decide)
  have hpre : PrePowers base pow := hs.advance (hp.keep.mono (by simp)) hcrit hbody hone
  refine WP.mono (entryFinish_ok pow) fun t ht => ?_
  subst t
  have hf := (VG.Proof.Aes.PPC64LE.Crypto.Local.write pow .r11 (pow.gpr .r24)).trans
    (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r12 (pow.gpr .r4+1))
  have hpre' : PrePowers base ((pow.write .r11 (pow.gpr .r24)).write .r12 (pow.gpr .r4+1)) := by
    exact hpre.advance hf.keep (fun r _ => hf.v r (by simp))
      (by simpa only [hf.mem] using Frame.refl [coreBody base] pow.mem)
      (by rw [hf.mem])
  refine ⟨hpre',?_,?_,?_⟩
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
    exact hpre.cache
  · rw [RegUpd.gpr_write_self,hpre.keep.gpr (by decide)]
  · simpa only [RegUpd.mem_write,hs.table] using hp.ready


theorem code_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10])
    Impl.AesGcm.PPC64LE.Blocks.code h).isSome = true := ⟨_, by taint_decide⟩

theorem encrypt_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    Impl.AesGcm.PPC64LE.Blocks.encrypt h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.PPC64LE.Blocks
