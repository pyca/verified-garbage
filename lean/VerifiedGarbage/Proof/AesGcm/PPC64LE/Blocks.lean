module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.Aes.Memory
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Rounds

/-! # Polynomial arithmetic for the fused POWER8 bulk loop -/

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

theorem copyKey_ok (s : State) (h0 : s.gpr .r0 = 0)
    (hm : s.vpr .v19 = Impl.Aes.PPC64LE.Crypto.byteMask)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16)
    (hw : InRegions s.wr (s.gpr .r11) 16) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.copyKey) s (CopyKeyResult s) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.copyKey, WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.load_ok .v8 .r9 s (by decide) (by decide)
    h0 hm hr) fun u ⟨hv, hf⟩ => ?_
  have hwu : InRegions u.wr (u.gpr .r11+u.gpr .r0) 16 := by
    simpa only [hf.wr, hf.gpr, h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw
  refine WP.mono (rawStore_ok .v8 .r11 .r0 u (by decide) hwu) fun t ht => ?_
  subst t
  refine ⟨?_, ?_, hv, ?_⟩
  · exact ⟨fun r _ => congrFun hf.gpr r, hf.rd, hf.wr⟩
  · intro r hr
    exact hf.v r (by simpa only [List.mem_singleton] using hr)
  · change u.mem.write (u.gpr .r11+u.gpr .r0) 16 (swapDwords (u.vpr .v8)) = _
    rw [hf.mem, hf.gpr, hv, h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero]

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


theorem code_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10])
    Impl.AesGcm.PPC64LE.Blocks.code h).isSome = true := ⟨_, by taint_decide⟩

theorem encrypt_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    Impl.AesGcm.PPC64LE.Blocks.encrypt h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.PPC64LE.Blocks
