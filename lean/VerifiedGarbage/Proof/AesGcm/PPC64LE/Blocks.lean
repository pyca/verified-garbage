module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Callee
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.CtrFinish
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
    {j : Nat} (hj : j < 9)
    (key : VG.Proof.Aes.PPC64LE.Crypto.IsKey (base.vpr (keyReg j)) (Spec.Aes.roundKey w (j+1))) (s : State)
    (hs : EarlyInv base nr w input j s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.cipherRegs false false (keyReg j)
      (Impl.AesGcm.PPC64LE.Blocks.rs 8))) s (EarlyInv base nr w input (j+1)) := by
  have facts : ∀ j : Fin 9, keyReg j ∉ Impl.AesGcm.PPC64LE.Blocks.rs 8 := by decide
  have hk := facts ⟨j, hj⟩
  have hkey : VG.Proof.Aes.PPC64LE.Crypto.IsKey (s.vpr (keyReg j)) (Spec.Aes.roundKey w (j+1)) := by
    rw [hs.effects.v _ hk]
    exact key
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

theorem keyRoundsRange_ok (nr : Nat) (w : List Byte) (input : Nat → Spec.Aes.State) (s : State)
    (start count : Nat) (hbound : start+count≤9)
    (keys : ∀ j, start≤j → j<start+count →
      VG.Proof.Aes.PPC64LE.Crypto.IsKey (s.vpr (keyReg j)) (Spec.Aes.roundKey w (j+1)))
    (hval : ∀ i < 8, aesState (cipherAt s i)=
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) start) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.keyRoundsRange start count)) s
      (EarlyInv s nr w input (start+count)) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.keyRoundsRange]
  apply wp_range_flatMap (M := isa) (N := count) (fun j => EarlyInv s nr w input (start+j))
    (fun j t hj ht => ?_) count (Nat.le_refl _) s ⟨VOnly.refl _ _,hval⟩
  simpa only [Nat.add_assoc,keyReg] using early_step s nr w input (j := start+j) (by omega)
    (keys (start+j) (by omega) (by omega)) t ht

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

theorem RawCfg.of_local {base s : State} {nr : Nat} {w : List Byte}
    {gs : List Reg} {vs : List VReg} (cfg : RawCfg base nr w)
    (hs : VG.Proof.Aes.PPC64LE.Crypto.Local gs vs base s)
    (h0 : .r0 ∉ gs) (h3 : .r3 ∉ gs) : RawCfg s nr w := by
  refine ⟨(hs.keep.gpr h0).trans cfg.zero,cfg.min,cfg.max,?_,?_⟩
  · intro j hj
    rw [hs.keep.2.1,hs.keep.2.2,hs.keep.gpr h3]; exact cfg.reads j hj
  · intro j hj
    rw [hs.mem,hs.keep.gpr h3]; exact cfg.keys j hj

theorem finalKeyPrefetch_ok (s : State) (nr : Nat) (w : List Byte) (cfg : RawCfg s nr w)
    (hr : s.gpr .r4=BitVec.ofNat 64 nr) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.finalKeyPrefetch) s fun t =>
      VG.Proof.Aes.PPC64LE.Crypto.IsKey (t.vpr .v9) (Spec.Aes.roundKey w nr) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local [.r12] [.v9] s t := by
  have hshift : BitVec.ofNat 64 nr <<< 4=BitVec.ofNat 64 (16*nr) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show nr<2^64 by have := cfg.max; omega)]
    simp only [Nat.shiftLeft_eq,Nat.reducePow,Nat.mul_comm]
  change WP isa (.block ([.lsl .r12 .r4 4]++[.lxvd2x .v9 .r3 .r12])) s _
  rw [WP.block_append_iff]
  have hs : WP isa (.block [.lsl .r12 .r4 4]) s (· = s.write .r12 (s.gpr .r4 <<< 4)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec_lsl (sh := 4) (by decide),
      Option.some.injEq,exists_eq_left']
  refine WP.mono hs fun u hu => ?_
  subst u
  have hread : InRegions ((s.write .r12 (s.gpr .r4 <<< 4)).rd++(s.write .r12 (s.gpr .r4 <<< 4)).wr)
      ((s.write .r12 (s.gpr .r4 <<< 4)).gpr .r3+(s.write .r12 (s.gpr .r4 <<< 4)).gpr .r12) 16 := by
    simp only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,hr,hshift]
    exact cfg.reads nr (Nat.le_refl _)
  refine WP.mono (rawLoad_ok .v9 .r3 .r12 _ (by decide) hread) fun t ⟨hv,hf⟩ => ?_
  refine ⟨?_,?_⟩
  · rw [hv]
    simpa only [RegUpd.mem_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,hr,hshift]
      using cfg.keys nr (Nat.le_refl _)
  · exact ((VG.Proof.Aes.PPC64LE.Crypto.Local.write s .r12 (s.gpr .r4 <<< 4)).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hf)).weaken (by simp) (by simp)

theorem keyRoundsPrefetched_ok (nr : Nat) (w : List Byte) (input : Nat → Spec.Aes.State) (s : State)
    (cfg : RawCfg s nr w) (hr : s.gpr .r4=BitVec.ofNat 64 nr)
    (keys : ∀ j < 9, VG.Proof.Aes.PPC64LE.Crypto.IsKey (s.vpr (keyReg j)) (Spec.Aes.roundKey w (j+1)))
    (values : ∀ i < 8, aesState (cipherAt s i)=
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 0) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.keyRoundsPrefetched) s fun t =>
      (∀ i < 8, aesState (cipherAt t i)=VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 9) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local [.r12] (.v9 :: Impl.AesGcm.PPC64LE.Blocks.rs 8) s t ∧
      VG.Proof.Aes.PPC64LE.Crypto.IsKey (t.vpr .v9) (Spec.Aes.roundKey w nr) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.keyRoundsPrefetched,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (keyRoundsRange_ok nr w input s 0 2 (by decide)
    (fun j _ hj => keys j (by omega)) values) fun u hu => ?_
  have cfgu := cfg.of_local (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hu.effects) (by simp) (by simp)
  have hru := (congrFun hu.effects.gpr .r4).trans hr
  refine WP.mono (finalKeyPrefetch_ok u nr w cfgu hru) fun v ⟨hfinal,hpref⟩ => ?_
  have keyFree : ∀ j : Fin 9, keyReg j.val ∉ Impl.AesGcm.PPC64LE.Blocks.rs 8 := by decide
  have keyNine : ∀ j : Fin 9, 2≤j.val → keyReg j.val≠.v9 := by decide
  have keys' : ∀ j, 2≤j → j<2+7 →
      VG.Proof.Aes.PPC64LE.Crypto.IsKey (v.vpr (keyReg j)) (Spec.Aes.roundKey w (j+1)) := by
    intro j hj hlt
    rw [hpref.v _ (by simpa only [List.mem_singleton] using keyNine ⟨j,by omega⟩ hj),
      hu.effects.v _ (keyFree ⟨j,by omega⟩)]
    exact keys j (by omega)
  have values' : ∀ i < 8, aesState (cipherAt v i)=
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 2 := by
    intro i hi
    have hfree : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i.val≠.v9 := by decide
    rw [cipherAt,hpref.v _ (by simpa only [List.mem_singleton] using hfree ⟨i,hi⟩)]
    exact hu.val i hi
  refine WP.mono (keyRoundsRange_ok nr w input v 2 7 (by decide) keys' values') fun t ht => ?_
  refine ⟨ht.val,?_,?_⟩
  · exact (((VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hu.effects).trans hpref).trans
      (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector ht.effects)).weaken (by simp) (by simp [or_left_comm])
  · rw [ht.effects.v .v9 (by decide)]; exact hfinal

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

theorem prefetched_last_ok {base : State} {nr : Nat} {w : List Byte} {input : Nat → Spec.Aes.State}
    {s : State} (h : RawInv base nr w input (nr-1) s)
    (hk : VG.Proof.Aes.PPC64LE.Crypto.IsKey (s.vpr .v9) (Spec.Aes.roundKey w nr)) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.finalRound) s fun t =>
      (∀ i < 8, aesState (cipherAt t i) = Spec.Aes.cipher nr w (input i)) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local [.r9,.r10]
        (.v8 :: Impl.AesGcm.PPC64LE.Blocks.rs 8) base t := by
  refine WP.mono (cipherStates_ok true .v9 (Impl.AesGcm.PPC64LE.Blocks.rs 8) s
    (by decide) (by decide) _ hk) fun t ⟨hv,hf⟩ => ⟨?_,?_⟩
  · intro i hi
    have hm : Impl.AesGcm.PPC64LE.Blocks.reg i ∈ Impl.AesGcm.PPC64LE.Blocks.rs 8 :=
      List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
    rw [cipherAt,hv _ hm]
    rw [show aesState (s.vpr (Impl.AesGcm.PPC64LE.Blocks.reg i)) =
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) (nr-1) from h.val i hi]
    exact VG.Proof.Aes.PPC64LE.Crypto.middle_last false nr w (input i)
  · exact (h.effects.trans (VG.Proof.Aes.PPC64LE.Crypto.Local.of_vector hf)).weaken
      (by simp) (by simp)

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
    (cfg : RawCfg base nr w) (hr : base.gpr .r4=BitVec.ofNat 64 nr)
    (known : ∀ i < 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      base.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1)))
    (values : ∀ i < 8, aesState (cipherAt base i)=
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 0) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.firstNine) base fun t =>
      (∀ i < 8, aesState (cipherAt t i)=VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 9) ∧
      VG.Proof.Aes.PPC64LE.Crypto.Local (.r9 :: Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs)
        (Impl.AesGcm.PPC64LE.Blocks.dataRegs++[T]++Impl.AesGcm.PPC64LE.Blocks.rs 8) base t ∧ DataOffsets t ∧
      VG.Proof.Aes.PPC64LE.Crypto.IsKey (t.vpr .v9) (Spec.Aes.roundKey w nr) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.firstNine,WP.block_append_iff]
  refine WP.mono (keyReads_ok base nr w cfg known) fun s ⟨hk,hf,hoff⟩ => ?_
  have hv : ∀ i < 8, aesState (cipherAt s i)=
      VG.Proof.Aes.PPC64LE.Crypto.middle false nr w (input i) 0 := by
    intro i hi
    have free : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ∉
        Impl.AesGcm.PPC64LE.Blocks.dataRegs++[T] := by decide
    rw [cipherAt,hf.v _ (free ⟨i,hi⟩)]
    exact values i hi
  have cfgs := cfg.of_local hf (by decide) (by decide)
  have hrs := (hf.keep.gpr (by decide)).trans hr
  refine WP.mono (keyRoundsPrefetched_ok nr w input s cfgs hrs hk hv) fun t ⟨ht,hg,hfinal⟩ => ?_
  refine ⟨ht,(hf.trans hg).weaken
    (by simp [Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs])
    (by simp [Impl.AesGcm.PPC64LE.Blocks.dataRegs]; intro a ha; simp [ha]),?_,hfinal⟩
  intro i hi
  have hfree : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.dataOffset i≠.r12 := by decide
  rw [hg.keep.gpr (by simpa only [List.mem_singleton] using hfree ⟨i,hi⟩)]
  exact hoff i hi


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
  refine WP.mono (firstNine_ok s nr w (fun i => aesState (cipherAt base i)) cfgs ((congrFun hf.gpr .r4).trans hr) knowns hv)
    fun u ⟨hu,hg,hoff,hfinal⟩ => ?_
  have cfgu : RawCfg u nr w := cfgs.of_local hg (by decide) (by decide)
  have hru : u.gpr .r4=BitVec.ofNat 64 nr :=
    (hg.keep.gpr (by decide)).trans ((congrFun hf.gpr .r4).trans hr)
  refine WP.mono (aesRemaining_ok u nr w (fun i => aesState (cipherAt base i)) cfgu hru hu)
    fun v hv => ?_
  apply WP.seq
  refine WP.mono (remaining_ok cfgu (show 9 ≤ nr-1 by have := cfg.min; omega) hv) fun z hz => ?_
  have hfinalz : VG.Proof.Aes.PPC64LE.Crypto.IsKey (z.vpr .v9) (Spec.Aes.roundKey w nr) := by
    rw [hz.effects.v .v9 (by decide)]
    exact hfinal
  refine WP.mono (prefetched_last_ok hz hfinalz) fun t ⟨ht,he⟩ => ?_
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


def cachedSchedule (base : State) (nr : Nat) : List Byte :=
  Spec.Aes.bytesAt base.mem (base.gpr .r3) (16*(nr+1))

theorem EntryResult.cacheCfg {base entry : State} {n nr : Nat} (lay : CoreLayout base n)
    (he : EntryResult base entry) (hnr : nr<15) (hr : base.gpr .r4=BitVec.ofNat 64 nr) :
    CacheCfg entry (nr+1) := by
  refine ⟨by omega,by omega,he.pre.zero,he.pre.mask,?_,?_,?_,?_⟩
  · rw [he.count,hr,BitVec.ofNat_add]
    rfl
  · intro j hj
    rw [he.pre.keep.2.1,he.pre.keep.2.2,he.pre.source]
    exact lay.key_read (by omega)
  · intro j hj
    rw [he.pre.keep.2.2,he.dest]
    change InRegions base.wr (base.gpr .r10+BitVec.ofNat 64 384+BitVec.ofNat 64 (16*j)) 16
    rw [Offset.add_add]
    exact lay.work_write (by omega)
  · rw [he.pre.source,he.dest]
    exact ((lay.scratch (coreKey base) (by simp)).sub_left (Region.sub_prefix (by omega))).sub_right
      (Offset.sub_base _ (d := 384) (n := 16*(nr+1)) (k := 2048) (by omega))

theorem EntryResult.key_read {base entry : State} {n nr : Nat} (lay : CoreLayout base n)
    (he : EntryResult base entry) (hnr : nr<15) {j : Nat} (hj : j≤nr) :
    VG.Proof.Aes.PPC64LE.Crypto.IsKey
      (rev128 (entry.mem.read (entry.gpr .r9+BitVec.ofNat 64 (16*j)) 16))
      (Spec.Aes.roundKey (cachedSchedule base nr) j) := by
  have hf : Frame [coreWork base] base.mem entry.mem :=
    lay.saved_frame.trans (coreBody_frame he.pre.frame)
  have hbytes : Spec.Aes.bytesAt entry.mem (base.gpr .r3) (16*(nr+1))=cachedSchedule base nr :=
    VG.Proof.Aes.Memory.bytesAt_frame (D := base.gpr .r10) (n := 128) (R := coreKey base) hf
      (lay.scratch (coreKey base) (by simp)) (by change 16*(nr+1) ≤ 256; omega) (by change 256 ≤ 2^64; decide)
  rw [he.pre.source]
  have hk := VG.Proof.Aes.PPC64LE.Crypto.key_read entry.mem (base.gpr .r3)
    (L := 16*(nr+1)) (j := j) (by omega)
  rw [hbytes] at hk
  exact hk

def KeysAt (m : Mem) (p : Addr) (nr : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ nr, VG.Proof.Aes.PPC64LE.Crypto.IsKey
    (swapDwords (m.read (p+BitVec.ofNat 64 (256+16*j)) 16)) (Spec.Aes.roundKey w j)

theorem cacheKeys_entry_ok (base entry : State) (n nr : Nat) (lay : CoreLayout base n)
    (he : EntryResult base entry) (hnr : nr<15) (hr : base.gpr .r4=BitVec.ofNat 64 nr) :
    WP isa (.loop (.block Impl.AesGcm.PPC64LE.Blocks.cacheStep) (.nonzero .d .r12)) entry fun t =>
      CacheInv entry (nr+1) (nr+1) t ∧
      KeysAt t.mem (base.gpr .r10+128) nr (cachedSchedule base nr) := by
  refine WP.mono (cacheKeys_ok entry (nr+1) (he.cacheCfg lay hnr hr)) fun t ht => ⟨ht,?_⟩
  intro j hj
  have hk := cachedKey_isKey ht (show j<nr+1 by omega) (he.key_read lay hnr hj)
  rw [he.dest] at hk
  change VG.Proof.Aes.PPC64LE.Crypto.IsKey
    (swapDwords (t.mem.read (base.gpr .r10+BitVec.ofNat 64 384+BitVec.ofNat 64 (16*j)) 16)) _ at hk
  change VG.Proof.Aes.PPC64LE.Crypto.IsKey
    (swapDwords (t.mem.read (base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 (256+16*j)) 16)) _
  rw [Offset.add_add] at hk ⊢
  simpa only [show 384+16*j=128+(256+16*j) by omega] using hk


theorem PowersAt.frame {m m' : Mem} {p : Addr} {h : BitVec 128} {rs : List Region}
    (hs : PowersAt m p h) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p+128,128⟩ : Region).Disjoint r) : PowersAt m' p h := by
  intro j hj
  have hl := hf.read (Offset.contains p (d := 128+32*j) (n := 16) (e := 128) (k := 128)
    (by omega) (by omega) (by decide)) hd (by decide)
  have hh := hf.read (Offset.contains p (d := 144+32*j) (n := 16) (e := 128) (k := 128)
    (by omega) (by omega) (by decide)) hd (by decide)
  rw [hl,hh]
  exact hs j hj

theorem KeysAt.frame {m m' : Mem} {p : Addr} {nr : Nat} {w : List Byte} {rs : List Region}
    (hs : KeysAt m p nr w) (hnr : nr<15) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p+256,240⟩ : Region).Disjoint r) : KeysAt m' p nr w := by
  intro j hj
  rw [hf.read (Offset.contains p (d := 256+16*j) (n := 16) (e := 256) (k := 240)
    (by omega) (by omega) (by decide)) hd (by decide)]
  exact hs j hj

def OneAt (m : Mem) (p : Addr) : Prop := swapDwords (m.read (p+16) 16)=1

theorem OneAt.frame {m m' : Mem} {p : Addr} {rs : List Region}
    (hs : OneAt m p) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p+16,16⟩ : Region).Disjoint r) : OneAt m' p := by
  rw [OneAt,hf.read (Region.contains_self _ _) hd (by decide)]
  exact hs

structure Tables (m : Mem) (p : Addr) (h : BitVec 128) (nr : Nat) (w : List Byte) : Prop where
  keys : KeysAt m p nr w
  powers : PowersAt m p (VG.Proof.Gcm.PPC64LE.Vpmsum.adjustedKey h)
  one : OneAt m p

theorem Tables.frame {m m' : Mem} {p : Addr} {h : BitVec 128} {nr : Nat} {w : List Byte} {rs : List Region}
    (hs : Tables m p h nr w) (hnr : nr<15) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p,512⟩ : Region).Disjoint r) : Tables m' p h nr w := by
  exact ⟨hs.keys.frame hnr hf (fun r hr => (hd r hr).sub_left (Offset.sub_base p (by decide))),
    hs.powers.frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base p (by decide))),
    hs.one.frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base p (by decide)))⟩

theorem Tables.counter {m m' : Mem} {p : Addr} {h : BitVec 128} {nr : Nat} {w : List Byte}
    (hs : Tables m p h nr w) (hnr : nr<15) (hf : Frame [⟨p+112,16⟩] m m') : Tables m' p h nr w := by
  have hk : (⟨p+256,240⟩ : Region).Disjoint ⟨p+112,16⟩ :=
    Offset.disjoint p (Or.inr (by decide)) (by decide) (by decide)
  have hp : (⟨p+128,128⟩ : Region).Disjoint ⟨p+112,16⟩ :=
    Offset.disjoint p (Or.inr (by decide)) (by decide) (by decide)
  have ho : (⟨p+16,16⟩ : Region).Disjoint ⟨p+112,16⟩ :=
    Offset.disjoint p (Or.inl (by decide)) (by decide) (by decide)
  exact ⟨hs.keys.frame hnr hf (by simpa only [List.mem_singleton,forall_eq] using hk),
    hs.powers.frame hf (by simpa only [List.mem_singleton,forall_eq] using hp),
    hs.one.frame hf (by simpa only [List.mem_singleton,forall_eq] using ho)⟩


theorem EntryResult.cacheDest {base entry : State} (he : EntryResult base entry) :
    entry.gpr .r11=(base.gpr .r10+128)+256 := by
  rw [he.dest]
  change base.gpr .r10+BitVec.ofNat 64 384=base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 256
  rw [Offset.add_add]

structure CachedKeysResult (base entry : State) (nr : Nat) (s : State) : Prop where
  inv : CacheInv entry (nr+1) (nr+1) s
  frame : Frame [coreBody base] (coreSavedMem base) s.mem
  tables : Tables s.mem (base.gpr .r10+128) (Spec.Gcm.ctxH base.mem (base.gpr .r3)) nr (cachedSchedule base nr)

theorem cacheKeys_tables_ok (base entry : State) (n nr : Nat) (lay : CoreLayout base n)
    (he : EntryResult base entry) (hnr : nr<15) (hr : base.gpr .r4=BitVec.ofNat 64 nr) :
    WP isa (.loop (.block Impl.AesGcm.PPC64LE.Blocks.cacheStep) (.nonzero .d .r12)) entry
      (CachedKeysResult base entry nr) := by
  refine WP.mono (cacheKeys_entry_ok base entry n nr lay he hnr hr) fun s ⟨hs,hk⟩ => ?_
  have hf : Frame [coreBody base] entry.mem s.mem := hs.frame.sub (fun r hmem => by
    rw [List.mem_singleton] at hmem
    subst r
    refine ⟨coreBody base,List.mem_singleton_self _,?_⟩
    rw [he.cacheDest]
    exact Offset.sub_base _ (d := 256) (n := 16*(nr+1)) (k := 1920) (by omega))
  have hp : PowersAt s.mem (base.gpr .r10+128)
      (VG.Proof.Gcm.PPC64LE.Vpmsum.adjustedKey (Spec.Gcm.ctxH base.mem (base.gpr .r3))) := by
    refine he.powers.frame hs.frame ?_
    intro r hmem
    rw [List.mem_singleton] at hmem
    subst r
    rw [he.cacheDest]
    exact Offset.disjoint _ (d := 128) (n := 128) (e := 256) (k := 16*(nr+1))
      (Or.inl (by decide)) (by decide) (by omega)
  have ho : OneAt entry.mem (base.gpr .r10+128) := by
    change swapDwords (entry.mem.read (base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 16) 16)=1
    rw [Offset.add_add]
    exact he.pre.one
  have ho' : OneAt s.mem (base.gpr .r10+128) := by
    refine ho.frame hs.frame ?_
    intro r hmem
    rw [List.mem_singleton] at hmem
    subst r
    rw [he.cacheDest]
    exact Offset.disjoint _ (d := 16) (n := 16) (e := 256) (k := 16*(nr+1))
      (Or.inl (by decide)) (by decide) (by omega)
  exact ⟨hs,he.pre.frame.trans hf,⟨hk,hp,ho'⟩⟩

theorem cacheSelect_ok (base : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.cacheSelect) base
      (· = ((base.write .r3 (base.gpr .r24)).write .r23 64).write .r24 80) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.cacheSelect,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    exec_li (imm := 64) (by decide),exec_li (imm := 80) (by decide),Option.some.injEq,exists_eq_left']
  rfl


def loopGprs : List Reg := [.r6,.r7,.r8,.r9,.r10,.r11,.r12,.r21,.r22]

structure LoopFixed (base : State) (nr : Nat) (s : State) : Prop where
  rd : s.rd=base.rd
  wr : s.wr=base.wr
  zero : s.gpr .r0=0
  keysPtr : s.gpr .r3=base.gpr .r10+384
  rounds : s.gpr .r4=BitVec.ofNat 64 nr
  counter : s.gpr .r5=base.gpr .r5
  yPtr : s.gpr .r14=base.gpr .r9
  counterOffset : s.gpr .r15=112
  table : s.gpr .r16=base.gpr .r10+128
  dataOffset : s.gpr .r18=96
  oneOffset : s.gpr .r20=16
  offset64 : s.gpr .r23=64
  offset80 : s.gpr .r24=80
  mask : s.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask
  poly : s.vpr .v13=poly++poly
  tables : Tables s.mem (base.gpr .r10+128) (Spec.Gcm.ctxH base.mem (base.gpr .r3)) nr (cachedSchedule base nr)

theorem LoopFixed.update {base s t : State} {nr : Nat} (hs : LoopFixed base nr s)
    (hk : Keep loopGprs s t) (hm : t.vpr .v19=s.vpr .v19) (hp : t.vpr .v13=s.vpr .v13)
    (ht : Tables t.mem (base.gpr .r10+128) (Spec.Gcm.ctxH base.mem (base.gpr .r3)) nr (cachedSchedule base nr)) :
    LoopFixed base nr t := by
  exact ⟨hk.2.1.trans hs.rd,hk.2.2.trans hs.wr,
    (hk.gpr (by decide)).trans hs.zero,(hk.gpr (by decide)).trans hs.keysPtr,
    (hk.gpr (by decide)).trans hs.rounds,(hk.gpr (by decide)).trans hs.counter,
    (hk.gpr (by decide)).trans hs.yPtr,(hk.gpr (by decide)).trans hs.counterOffset,
    (hk.gpr (by decide)).trans hs.table,(hk.gpr (by decide)).trans hs.dataOffset,
    (hk.gpr (by decide)).trans hs.oneOffset,(hk.gpr (by decide)).trans hs.offset64,
    (hk.gpr (by decide)).trans hs.offset80,hm.trans hs.mask,hp.trans hs.poly,ht⟩

theorem LoopFixed.table_write {base s : State} {nr n off len : Nat} (hs : LoopFixed base nr s)
    (lay : CoreLayout base n) (ho : off+len ≤ 512) :
    InRegions s.wr (s.gpr .r16+BitVec.ofNat 64 off) len := by
  rw [hs.wr,hs.table]
  change InRegions base.wr (base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 off) len
  rw [Offset.add_add]
  exact lay.work_write (by omega)

theorem LoopFixed.rawCfg {base s : State} {nr n : Nat} (hs : LoopFixed base nr s)
    (lay : CoreLayout base n) (hmin : 9<nr) (hmax : nr<15) : RawCfg s nr (cachedSchedule base nr) := by
  refine ⟨hs.zero,hmin,hmax,?_,?_⟩
  · intro j hj
    rw [hs.rd,hs.wr,hs.keysPtr]
    have hw := lay.work_write (offset := 384+16*j) (len := 16) (by omega)
    obtain ⟨r,hr,hp⟩ := hw
    refine ⟨r,List.mem_append_right _ hr,?_⟩
    change r.Contains (base.gpr .r10+BitVec.ofNat 64 384+BitVec.ofNat 64 (16*j)) 16
    rw [Offset.add_add]
    exact hp
  · intro j hj
    rw [hs.keysPtr]
    have hk := hs.tables.keys j hj
    change VG.Proof.Aes.PPC64LE.Crypto.IsKey
      (swapDwords (s.mem.read (base.gpr .r10+BitVec.ofNat 64 128+BitVec.ofNat 64 (256+16*j)) 16)) _ at hk
    change VG.Proof.Aes.PPC64LE.Crypto.IsKey
      (swapDwords (s.mem.read (base.gpr .r10+BitVec.ofNat 64 384+BitVec.ofNat 64 (16*j)) 16)) _
    rw [Offset.add_add] at hk ⊢
    simpa only [show 128+(256+16*j)=384+16*j by omega] using hk

theorem LoopFixed.key_offsets {base s : State} {nr : Nat} (hs : LoopFixed base nr s) :
    ∀ i < 8, Impl.AesGcm.PPC64LE.Blocks.keyOffset i ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
      s.gpr (Impl.AesGcm.PPC64LE.Blocks.keyOffset i)=BitVec.ofNat 64 (16*(i+1)) := by
  intro i hi hn
  have choices : ∀ j : Fin 8,
      Impl.AesGcm.PPC64LE.Blocks.keyOffset j ∉ Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs →
        j.val=0 ∨ j.val=3 ∨ j.val=4 ∨ j.val=5 := by decide
  have hcases : i=0 ∨ i=3 ∨ i=4 ∨ i=5 := choices ⟨i,hi⟩ hn
  rcases hcases with h | h | h | h
  · subst i; exact hs.oneOffset
  · subst i; exact hs.offset64
  · subst i; exact hs.offset80
  · subst i; exact hs.dataOffset


theorem cacheSelect_fixed (base entry keys : State) (nr : Nat)
    (he : EntryResult base entry) (hk : CachedKeysResult base entry nr keys)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.cacheSelect) keys fun s =>
      LoopFixed base nr s ∧ VG.Proof.Aes.PPC64LE.Crypto.Local [.r3,.r23,.r24] [] keys s := by
  refine WP.mono (cacheSelect_ok keys) fun s hs => ?_
  subst s
  have hl := ((VG.Proof.Aes.PPC64LE.Crypto.Local.write keys .r3 (keys.gpr .r24)).trans
    (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r23 64)).trans
    (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r24 80)
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,hl.weaken (by simp) (by simp)⟩
  · simpa only [RegUpd.rd_write] using hk.inv.keep.2.1.trans he.pre.keep.2.1
  · simpa only [RegUpd.wr_write] using hk.inv.keep.2.2.trans he.pre.keep.2.2
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using (hk.inv.keep.gpr (r := .r0) (by decide)).trans he.pre.zero
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true] using (hk.inv.keep.gpr (r := .r24) (by decide)).trans he.pre.cache
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using
      (hk.inv.keep.gpr (r := .r4) (by decide)).trans ((he.pre.keep.gpr (by decide)).trans hr)
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using
      (hk.inv.keep.gpr (r := .r5) (by decide)).trans (he.pre.keep.gpr (by decide))
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using
      (hk.inv.keep.gpr (r := .r14) (by decide)).trans he.pre.yPtr
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using
      (hk.inv.keep.gpr (r := .r15) (by decide)).trans he.pre.counterOffset
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using
      (hk.inv.keep.gpr (r := .r16) (by decide)).trans he.pre.table
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using
      (hk.inv.keep.gpr (r := .r18) (by decide)).trans he.pre.dataOffset
  · simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using
      (hk.inv.keep.gpr (r := .r20) (by decide)).trans he.pre.oneOffset
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false]
  · exact RegUpd.gpr_write_self ..
  · simpa only [vpr_write] using (hk.inv.v .v19 (by decide)).trans he.pre.mask
  · simpa only [vpr_write] using (hk.inv.v .v13 (by decide)).trans he.pre.poly
  · simpa only [RegUpd.mem_write] using hk.tables


def cacheGprs : List Reg := [.r9,.r11,.r12,.r3,.r23,.r24]

structure CacheResult (base entry : State) (nr : Nat) (s : State) : Prop where
  keep : Keep cacheGprs entry s
  frame : Frame [coreBody base] (coreSavedMem base) s.mem
  fixed : LoopFixed base nr s
  data : s.gpr .r6=base.gpr .r6
  left : s.gpr .r7=base.gpr .r7
  word : (s.gpr .r8).setWidth 32=(Spec.Gcm.blockAt base.mem (base.gpr .r5)).extractLsb' 0 32
  y : s.vpr .v10=Spec.Gcm.blockAt base.mem (base.gpr .r9)
  counter : swapDwords (s.mem.read ((base.gpr .r10+128)+112) 16)=Spec.Gcm.blockAt base.mem (base.gpr .r5)

theorem cache_ok (base entry : State) (n nr : Nat) (lay : CoreLayout base n)
    (he : EntryResult base entry) (hnr : nr<15) (hr : base.gpr .r4=BitVec.ofNat 64 nr) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.cache entry (CacheResult base entry nr) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.cache]
  apply WP.seq
  refine WP.mono (cacheKeys_tables_ok base entry n nr lay he hnr hr) fun keys hk => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cacheSelect_fixed base entry keys nr he hk hr) fun selected ⟨fx,hs⟩ => ?_
  have hread : InRegions (selected.rd++selected.wr) (selected.gpr .r5) 16 := by
    rw [fx.rd,fx.wr,fx.counter]
    obtain ⟨r,hr,hp⟩ := lay.writes _ _ ⟨coreCounter base,by simp,Region.contains_self _ _⟩
    exact ⟨r,List.mem_append_right _ hr,hp⟩
  have hwrite : InRegions selected.wr (selected.gpr .r16+selected.gpr .r15) 16 := by
    rw [fx.counterOffset]
    exact fx.table_write lay (off := 112) (len := 16) (by decide)
  have hframe : Frame [coreWork base] base.mem selected.mem := by
    simpa only [hs.mem] using lay.saved_frame.trans (coreBody_frame hk.frame)
  have hcb : rev128 (selected.mem.read (selected.gpr .r5) 16)=Spec.Gcm.blockAt base.mem (base.gpr .r5) := by
    rw [VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,fx.counter]
    exact lay.input_block (r := coreCounter base) hframe (by simp) (Region.contains_self _ _)
  refine WP.mono (cacheLoad_ok .v0 .r5 .r16 .r15 selected (by decide) (by decide) (by decide)
    fx.zero fx.mask hread hwrite) fun t ht => ?_
  have hmem : t.mem=keys.mem.write ((base.gpr .r10+128)+112) 16
      (swapDwords (Spec.Gcm.blockAt base.mem (base.gpr .r5))) := by
    rw [ht.mem,hcb,fx.table,fx.counterOffset,hs.mem]
  have hcf : Frame [⟨(base.gpr .r10+128)+112,16⟩] keys.mem t.mem := by
    rw [hmem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hbf : Frame [coreBody base] keys.mem t.mem := hcf.sub (fun r hr => by
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨coreBody base,List.mem_singleton_self _,
      Offset.sub_base _ (d := 112) (n := 16) (k := 1920) (by decide)⟩)
  have hkeep : Keep cacheGprs entry t :=
    ((hk.inv.keep.trans hs.keep).trans ht.keep).mono (by simp [cacheGprs])
  refine ⟨hkeep,hk.frame.trans hbf,?_,?_,?_,?_,?_,?_⟩
  · exact fx.update (ht.keep.mono (by simp)) (ht.v .v19 (by decide)) (ht.v .v13 (by decide))
      (hk.tables.counter hnr hcf)
  · exact (hkeep.gpr (by decide)).trans (he.pre.keep.gpr (by decide))
  · exact (hkeep.gpr (by decide)).trans (he.pre.keep.gpr (by decide))
  · rw [hkeep.gpr (by decide)]; exact he.pre.word
  · exact (ht.v .v10 (by decide)).trans ((hs.v .v10 (by simp)).trans ((hk.inv.v .v10 (by decide)).trans he.pre.y))
  · rw [hmem,VG.Proof.VectorCrypto.read_write16,swapDwords_involutive]


theorem LoopFixed.table_read {base s : State} {nr n off len : Nat} (hs : LoopFixed base nr s)
    (lay : CoreLayout base n) (ho : off+len ≤ 512) :
    InRegions (s.rd++s.wr) (s.gpr .r16+BitVec.ofNat 64 off) len := by
  obtain ⟨r,hr,hp⟩ := hs.table_write lay ho
  exact ⟨r,List.mem_append_right _ hr,hp⟩

theorem counters_fixed (base start : State) (n nr : Nat) (cb : Spec.Gcm.Block)
    (lay : CoreLayout base n) (fx : LoopFixed base nr start) (hnr : nr<15)
    (hcb : swapDwords (start.mem.read ((base.gpr .r10+128)+112) 16)=cb) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.counters 8)) start fun t =>
      CountersResult start cb t ∧ LoopFixed base nr t ∧ Frame [coreBody base] start.mem t.mem ∧
      swapDwords (t.mem.read ((base.gpr .r10+128)+112) 16)=Nat.repeat Spec.Gcm.inc32 8 cb := by
  have hrc : InRegions (start.rd++start.wr) (start.gpr .r16+start.gpr .r15) 16 := by
    rw [fx.counterOffset]; exact fx.table_read lay (off := 112) (len := 16) (by decide)
  have hr1 : InRegions (start.rd++start.wr) (start.gpr .r16+start.gpr .r20) 16 := by
    rw [fx.oneOffset]; exact fx.table_read lay (off := 16) (len := 16) (by decide)
  have hw : InRegions start.wr (start.gpr .r16+start.gpr .r15) 16 := by
    rw [fx.counterOffset]; exact fx.table_write lay (off := 112) (len := 16) (by decide)
  have hc : swapDwords (start.mem.read (start.gpr .r16+start.gpr .r15) 16)=cb := by
    simpa only [fx.table,fx.counterOffset] using hcb
  have ho : swapDwords (start.mem.read (start.gpr .r16+start.gpr .r20) 16)=0#96++1#32 := by
    simpa only [fx.table,fx.oneOffset,OneAt,show (1 : BitVec 128)=0#96++1#32 from rfl] using fx.tables.one
  refine WP.mono (counters_ok start cb hrc hr1 hw hc ho) fun t ht => ?_
  have hcf : Frame [⟨(base.gpr .r10+128)+112,16⟩] start.mem t.mem := by
    rw [ht.mem,fx.table,fx.counterOffset]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨ht,?_,?_,?_⟩
  · exact fx.update (ht.keep.mono (by simp [loopGprs])) (ht.v .v19 (by decide)) (ht.v .v13 (by decide))
      (fx.tables.counter hnr hcf)
  · exact hcf.sub (fun r hr => by
      rw [List.mem_singleton] at hr
      subst r
      exact ⟨coreBody base,List.mem_singleton_self _,
        Offset.sub_base _ (d := 112) (n := 16) (k := 1920) (by decide)⟩)
  · rw [ht.mem,fx.table,fx.counterOffset,VG.Proof.VectorCrypto.read_write16,swapDwords_involutive]

theorem scalar_counter_step (cb : Spec.Gcm.Block) (word : BitVec 64)
    (hw : word.setWidth 32=cb.extractLsb' 0 32) :
    (word+8).setWidth 32=(Nat.repeat Spec.Gcm.inc32 8 cb).extractLsb' 0 32 := by
  rw [BitVec.setWidth_add word 8 (by decide),hw,VG.Proof.Aes.repeat_inc32_lo]
  rfl

def aesGprs : List Reg := [.r9,.r10]++Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs

def aesVprs : List VReg :=
  .v8 :: (Impl.AesGcm.PPC64LE.Blocks.rs 8++Impl.AesGcm.PPC64LE.Blocks.dataRegs++[T])

theorem aes8_fixed (base start : State) (n nr : Nat) (lay : CoreLayout base n)
    (fx : LoopFixed base nr start) (hmin : 9<nr) (hmax : nr<15) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.aes8 start fun t =>
      (∀ i < 8, cipherAt t i=Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr (cipherAt start i)) ∧
      LoopFixed base nr t ∧ DataOffsets t ∧ VG.Proof.Aes.PPC64LE.Crypto.Local aesGprs aesVprs start t := by
  refine WP.mono (aes8_ok start nr (cachedSchedule base nr) (fx.rawCfg lay hmin hmax) fx.rounds fx.key_offsets)
    fun t ⟨hv,hf,hoff⟩ => ?_
  refine ⟨?_,?_,hoff,hf⟩
  · intro i hi
    apply VG.Proof.Aes.PPC64LE.Crypto.aesState_inj
    change aesState (cipherAt t i)=aesState (Spec.Gcm.aesWith nr (cachedSchedule base nr) (cipherAt start i))
    rw [VG.Proof.Aes.PPC64LE.Crypto.aesState_aesWith]
    exact hv i hi
  · exact fx.update (hf.keep.mono (by simp [loopGprs,Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs]))
      (hf.v .v19 (by decide)) (hf.v .v13 (by decide)) (by simpa only [hf.mem] using fx.tables)


def cipherBlock (base : State) (nr i : Nat) : Spec.Gcm.Block :=
  Spec.Gcm.blockAt base.mem (base.gpr .r6+BitVec.ofNat 64 (16*i)) ^^^
    Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr (Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt base.mem (base.gpr .r5)))

def cipherState (base : State) (nr i : Nat) : Spec.Aes.State := aesState (cipherBlock base nr i)

def hashPrefix (base : State) (nr k : Nat) : Spec.Gcm.Block :=
  Spec.Gcm.ghashFrom (Spec.Gcm.ctxH base.mem (base.gpr .r3)) (Spec.Gcm.blockAt base.mem (base.gpr .r9))
    ((List.range k).map (cipherBlock base nr))

theorem hashPrefix_add (base : State) (nr k j : Nat) :
    hashPrefix base nr (k+j)=Spec.Gcm.ghashFrom (Spec.Gcm.ctxH base.mem (base.gpr .r3))
      (hashPrefix base nr k) ((List.range j).map (fun i => cipherBlock base nr (k+i))) := by
  simp only [hashPrefix,List.range_add,List.map_append,List.map_map,Spec.Gcm.ghashFrom,List.foldl_append]
  rfl

theorem repeat_counter_add (cb : Spec.Gcm.Block) (k i : Nat) :
    Nat.repeat Spec.Gcm.inc32 i (Nat.repeat Spec.Gcm.inc32 k cb)=Nat.repeat Spec.Gcm.inc32 (k+i) cb := by
  calc
    _ = (Nat.repeat Spec.Gcm.inc32 k cb).extractLsb' 32 96 ++
        ((Nat.repeat Spec.Gcm.inc32 k cb).extractLsb' 0 32+BitVec.ofNat 32 i) := counterValue _ _
    _ = _ := counter_advance cb k i

theorem processed_original_block {m₀ m : Mem} {D : Addr} {n k j : Nat} {F : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.Memory.Processed m₀ m D n k F) (hj : k≤j) (hjn : j<n) :
    Spec.Gcm.blockAt m (D+BitVec.ofNat 64 (16*j))=Spec.Gcm.blockAt m₀ (D+BitVec.ofNat 64 (16*j)) := by
  apply VG.Proof.Aes.PPC64LE.Crypto.aesState_inj
  rw [VG.Proof.Aes.PPC64LE.Crypto.aesState_blockAt,VG.Proof.Aes.PPC64LE.Crypto.aesState_blockAt]
  exact hp.original hj hjn


theorem stores_fixed (base start : State) (n nr k : Nat) (lay : CoreLayout base n)
    (fx : LoopFixed base nr start) (hmax : nr<15) (hk : k+8≤n)
    (ptr : start.gpr .r6=base.gpr .r6+BitVec.ofNat 64 (16*k)) (offsets : DataOffsets start)
    (hp : VG.Proof.Aes.Memory.Processed base.mem start.mem (base.gpr .r6) n k (cipherState base nr))
    (values : ∀ i < 8, cipherAt start i=Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr
      (Nat.repeat Spec.Gcm.inc32 (k+i) (Spec.Gcm.blockAt base.mem (base.gpr .r5)))) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.stores) start fun t =>
      StoreBatchResult start base.mem (base.gpr .r6) n k (cipherState base nr) t ∧ LoopFixed base nr t ∧
      (∀ i < 8, cipherAt t i=cipherBlock base nr (k+i)) := by
  have hvalues : ∀ i < 8, ciphertextValue start i=cipherBlock base nr (k+i) := by
    intro i hi
    rw [ciphertextValue,values i hi,VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,ptr,Offset.add_add,
      show 16*k+16*i=16*(k+i) by omega,
      processed_original_block hp (show k≤k+i by omega) (show k+i<n by omega),BitVec.xor_comm]
    rfl
  have writes : ∀ i < 8, InRegions start.wr (base.gpr .r6+BitVec.ofNat 64 (16*(k+i))) 16 := by
    intro i hi
    rw [fx.wr]
    exact lay.writes _ _ ⟨coreData base n,by simp,
      Offset.contains_base _ (d := 16*(k+i)) (n := 16) (k := 16*n) (by omega) (by have := lay.size; omega)⟩
  have reads : ∀ i < 8, InRegions (start.rd++start.wr) (start.gpr .r6+BitVec.ofNat 64 (16*i)) 16 := by
    intro i hi
    rw [ptr,Offset.add_add,show 16*k+16*i=16*(k+i) by omega]
    obtain ⟨r,hr,hp⟩ := writes i hi
    exact ⟨r,List.mem_append_right _ hr,hp⟩
  have hstates : ∀ i < 8, aesState (ciphertextValue start i)=cipherState base nr (k+i) := by
    intro i hi; rw [hvalues i hi]; rfl
  refine WP.mono (stores_ok start base.mem (base.gpr .r6) n k (cipherState base nr) hk lay.size
    fx.mask ptr offsets reads writes hstates hp) fun t ht => ?_
  have hdis : (⟨base.gpr .r10+128,512⟩ : Region).Disjoint (coreData base n) :=
    (lay.scratch (coreData base n) (by simp)).symm.sub_left
      (Offset.sub_base _ (d := 128) (n := 512) (k := 2048) (by decide))
  refine ⟨ht,?_,?_⟩
  · exact fx.update (ht.keep.mono (by simp [loopGprs])) (ht.v .v19 (by decide)) (ht.v .v13 (by decide))
      (fx.tables.frame hmax ht.frame (by simpa only [List.mem_singleton,forall_eq,coreData] using hdis))
  · intro i hi
    exact (ht.values i hi).trans (hvalues i hi)


theorem ghStart_ok (base : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.ghStart) base
      (· = (base.write .r21 128).write .r22 144) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.ghStart,runBlock_cons,runStep_some,runBlock_nil,
    exec_li (imm := 128) (by decide),exec_li (imm := 144) (by decide),Option.some.injEq,exists_eq_left']
  rfl

theorem ghSlot_offset (s : State) (r : Reg) (offset j : Nat) (hr : s.gpr r=BitVec.ofNat 64 offset) :
    ghSlot s r j=s.gpr .r16+BitVec.ofNat 64 (offset+32*j) := by
  rw [ghSlot,hr,BitVec.ofNat_add]

theorem LoopFixed.ghCfg {base s : State} {nr n : Nat} (fx : LoopFixed base nr s)
    (lay : CoreLayout base n) (h21 : s.gpr .r21=128) (h22 : s.gpr .r22=144) :
    GhFoldCfg s (VG.Proof.Gcm.PPC64LE.Vpmsum.adjustedKey (Spec.Gcm.ctxH base.mem (base.gpr .r3))) := by
  refine ⟨?_,?_,?_⟩
  · intro j hj
    rw [ghSlot_offset s .r21 128 j h21,ghSlot_offset s .r22 144 j h22]
    exact ⟨fx.table_read lay (by omega),fx.table_read lay (by omega)⟩
  · intro j hj
    rw [ghSlot_offset s .r21 128 j h21,fx.table]
    exact (fx.tables.powers j hj).1
  · intro j hj
    rw [ghSlot_offset s .r22 144 j h22,fx.table]
    exact (fx.tables.powers j hj).2

theorem gh_fixed [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (base start : State) (n nr : Nat) (lay : CoreLayout base n) (fx : LoopFixed base nr start) :
    WP isa (.block (Impl.AesGcm.PPC64LE.Blocks.ghStart++Impl.AesGcm.PPC64LE.Blocks.ghCode)) start fun t =>
      t.vpr .v10=Spec.Gcm.ghashFrom (Spec.Gcm.ctxH base.mem (base.gpr .r3)) (start.vpr .v10)
        ((List.range 8).map (cipherAt start)) ∧
      LoopFixed base nr t ∧ VG.Proof.Aes.PPC64LE.Crypto.Local [.r21,.r22] ghClobbers start t := by
  rw [WP.block_append_iff]
  refine WP.mono (ghStart_ok start) fun s hs => ?_
  subst s
  have he := (VG.Proof.Aes.PPC64LE.Crypto.Local.write start .r21 128).trans
    (VG.Proof.Aes.PPC64LE.Crypto.Local.write _ .r22 144)
  have fx' := fx.update (he.keep.mono (by simp [loopGprs])) (he.v .v19 (by simp)) (he.v .v13 (by simp))
    (by simpa only [he.mem] using fx.tables)
  have h21 : ((start.write .r21 128).write .r22 144).gpr .r21=128 := by
    simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
  have h22 : ((start.write .r21 128).write .r22 144).gpr .r22=144 := RegUpd.gpr_write_self ..
  refine WP.mono (ghFold_ghash _ _ (fx'.ghCfg lay h21 h22) fx'.poly) fun t ⟨ht,hf⟩ => ?_
  refine ⟨?_,?_,?_⟩
  · have hfun : cipherAt ((start.write .r21 128).write .r22 144)=cipherAt start := by
      funext i
      exact he.v (Impl.AesGcm.PPC64LE.Blocks.reg i) (by simp)
    simpa only [hfun,vpr_write] using ht
  · exact fx'.update (hf.keep.mono (by simp [loopGprs])) (hf.v .v19 (by decide)) (hf.v .v13 (by decide))
      (by simpa only [hf.mem] using fx'.tables)
  · exact (he.trans hf).weaken (by simp) (by simp)


structure LoopInv (base ready : State) (n nr k : Nat) (s : State) : Prop where
  bound : k≤n
  fixed : LoopFixed base nr s
  keep : Keep loopGprs ready s
  frame : Frame [coreBody base,coreData base n] ready.mem s.mem
  ptr : s.gpr .r6=base.gpr .r6+BitVec.ofNat 64 (16*k)
  left : s.gpr .r7=BitVec.ofNat 64 (n-k)
  processed : VG.Proof.Aes.Memory.Processed base.mem s.mem (base.gpr .r6) n k (cipherState base nr)
  counter : swapDwords (s.mem.read ((base.gpr .r10+128)+112) 16)=
    Nat.repeat Spec.Gcm.inc32 k (Spec.Gcm.blockAt base.mem (base.gpr .r5))
  word : (s.gpr .r8).setWidth 32=(Nat.repeat Spec.Gcm.inc32 k (Spec.Gcm.blockAt base.mem (base.gpr .r5))).extractLsb' 0 32
  y : s.vpr .v10=hashPrefix base nr k

theorem LoopInv.initial {base entry ready : State} {n nr : Nat} (lay : CoreLayout base n)
    (hr : CacheResult base entry nr ready) (hn : base.gpr .r7=BitVec.ofNat 64 n) :
    LoopInv base ready n nr 0 ready := by
  have hf : Frame [coreWork base] base.mem ready.mem := lay.saved_frame.trans (coreBody_frame hr.frame)
  have hp := (VG.Proof.Aes.Memory.Processed.refl base.mem (base.gpr .r6) n (cipherState base nr)).frame hf
    (by simpa only [List.mem_singleton,forall_eq,coreData] using lay.scratch (coreData base n) (by simp)) lay.size
  refine ⟨by omega,hr.fixed,Keep.refl _ _,Frame.refl _ _,?_,?_,hp,hr.counter,hr.word,?_⟩
  · simpa only [Nat.mul_zero,BitVec.add_zero] using hr.data
  · rw [hr.left,hn,Nat.sub_zero]
  · simpa only [hashPrefix,List.range_zero,List.map_nil,Spec.Gcm.ghashFrom,List.foldl_nil] using hr.y


theorem batch_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {base ready s : State} {n nr k : Nat} (lay : CoreLayout base n)
    (hmin : 9<nr) (hmax : nr<15) (hk : k+8≤n) (hs : LoopInv base ready n nr k s) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.batch s (LoopInv base ready n nr (k+8)) := by
  let cb := Nat.repeat Spec.Gcm.inc32 k (Spec.Gcm.blockAt base.mem (base.gpr .r5))
  rw [Impl.AesGcm.PPC64LE.Blocks.batch]
  apply WP.seq
  refine WP.mono (counters_fixed base s n nr cb lay hs.fixed hmax hs.counter)
    fun ctr ⟨hc,fxc,hcf,hcb⟩ => ?_
  have hdataBody : (coreData base n).Disjoint (coreBody base) :=
    (lay.scratch (coreData base n) (by simp)).sub_right (coreBody_sub base)
  have hpc : VG.Proof.Aes.Memory.Processed base.mem ctr.mem (base.gpr .r6) n k (cipherState base nr) :=
    hs.processed.frame hcf (by simpa only [List.mem_singleton,forall_eq,coreData] using hdataBody) lay.size
  apply WP.seq
  refine WP.mono (aes8_fixed base ctr n nr lay fxc hmin hmax) fun aes ⟨ha,fxa,hoff,hfa⟩ => ?_
  have hpa : VG.Proof.Aes.Memory.Processed base.mem aes.mem (base.gpr .r6) n k (cipherState base nr) := by
    rw [hfa.mem]; exact hpc
  have ptra : aes.gpr .r6=base.gpr .r6+BitVec.ofNat 64 (16*k) :=
    (hfa.keep.gpr (by decide)).trans ((hc.keep.gpr (by decide)).trans hs.ptr)
  have vals : ∀ i < 8, cipherAt aes i=Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr
      (Nat.repeat Spec.Gcm.inc32 (k+i) (Spec.Gcm.blockAt base.mem (base.gpr .r5))) := by
    intro i hi
    rw [ha i hi,hc.values i hi]
    exact congrArg (Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr) (repeat_counter_add _ k i)
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (stores_fixed base aes n nr k lay fxa hmax hk ptra hoff hpa vals)
    fun stored ⟨hd,fxd,hvals⟩ => ?_
  refine WP.mono (gh_fixed base stored n nr lay fxd) fun t ⟨hy,fxg,hg⟩ => ?_
  have htableData : (⟨base.gpr .r10+128,512⟩ : Region).Disjoint (coreData base n) :=
    (lay.scratch (coreData base n) (by simp)).symm.sub_left
      (Offset.sub_base _ (d := 128) (n := 512) (k := 2048) (by decide))
  have hslotData : (⟨(base.gpr .r10+128)+112,16⟩ : Region).Disjoint (coreData base n) :=
    htableData.sub_left (Offset.sub_base _ (d := 112) (n := 16) (k := 512) (by decide))
  have hread : stored.mem.read ((base.gpr .r10+128)+112) 16=
      aes.mem.read ((base.gpr .r10+128)+112) 16 := hd.frame.read (Region.contains_self _ _)
        (by simpa only [List.mem_singleton,forall_eq,coreData] using hslotData) (by decide)
  have hctrFrame : Frame [coreBody base,coreData base n] s.mem ctr.mem := hcf.mono (by simp)
  have hstoreFrame : Frame [coreBody base,coreData base n] ctr.mem stored.mem := by
    rw [← hfa.mem]
    exact hd.frame.mono (by simp [coreData])
  have hyStored : stored.vpr .v10=hashPrefix base nr k :=
    (hd.v .v10 (by decide)).trans ((hfa.v .v10 (by decide)).trans ((hc.v .v10 (by decide)).trans hs.y))
  have hmap : (List.range 8).map (cipherAt stored)=
      (List.range 8).map (fun i => cipherBlock base nr (k+i)) := by
    exact List.map_congr_left fun i hi => hvals i (List.mem_range.mp hi)
  refine ⟨hk,fxg,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ((((hs.keep.trans hc.keep).trans hfa.keep).trans hd.keep).trans hg.keep).mono
      (by simp [loopGprs,aesGprs,Impl.AesGcm.PPC64LE.Blocks.keyOffsetRegs,or_left_comm,or_comm])
  · simpa only [hg.mem] using (hs.frame.trans hctrFrame).trans hstoreFrame
  · rw [hg.keep.gpr (by decide),hd.ptr,ptra]
    change base.gpr .r6+BitVec.ofNat 64 (16*k)+BitVec.ofNat 64 128=_
    rw [Offset.add_add]
    exact congrArg (fun i => base.gpr .r6+BitVec.ofNat 64 i) (by omega)
  · rw [hg.keep.gpr (by decide),hd.left,hfa.keep.gpr (by decide),hc.keep.gpr (by decide),hs.left]
    change BitVec.ofNat 64 (n-k)-BitVec.ofNat 64 8=_
    rw [Offset.ofNat_sub_ofNat (by omega),Nat.sub_sub]
  · simpa only [hg.mem] using hd.processed
  · rw [hg.mem,hread,hfa.mem,hcb]
    exact repeat_counter_add _ k 8
  · rw [hg.keep.gpr (by decide),hd.keep.gpr (by decide),hfa.keep.gpr (by decide),hc.scalar,
      scalar_counter_step cb (s.gpr .r8) hs.word]
    exact congrArg (fun x : BitVec 128 => x.extractLsb' 0 32) (repeat_counter_add _ k 8)
  · rw [hy,hyStored,hmap,hashPrefix_add]


theorem batches_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {base ready s : State} {n nr k : Nat} (lay : CoreLayout base n)
    (hmin : 9<nr) (hmax : nr<15) (hk : k+8≤n) (hm : (n-k)%8=0)
    (hs : LoopInv base ready n nr k s) :
    WP isa (.loop Impl.AesGcm.PPC64LE.Blocks.batch (.nonzero .d .r7)) s
      (LoopInv base ready n nr n) := by
  refine WP.loop (M := isa)
    (fun m t => ∃ j, m=n-j ∧ j+8≤n ∧ (n-j)%8=0 ∧ LoopInv base ready n nr j t)
    (fun m t ht => ?_) (n-k) s ⟨k,rfl,hk,hm,hs⟩
  obtain ⟨j,rfl,hj,hm,ht⟩ := ht
  refine WP.mono (batch_ok lay hmin hmax hj ht) fun u hu => ?_
  have hev : eval (.nonzero .d .r7) u=some (u.gpr .r7 != 0) := by
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq]
  by_cases he : j+8=n
  · left
    refine ⟨?_,he ▸ hu⟩
    rw [hu.left,he,Nat.sub_self] at hev
    exact hev.trans (by decide)
  · right
    have hne : u.gpr .r7 ≠ 0 := by
      intro hz
      have hh := congrArg BitVec.toNat hz
      rw [hu.left,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := lay.size; omega)] at hh
      exact he (by change n-(j+8)=0 at hh; omega)
    exact ⟨hev.trans (by simpa using hne),n-(j+8),by omega,j+8,rfl,by omega,by omega,hu⟩


def exitMem (s : State) : Mem :=
  (s.mem.writeW (s.gpr .r5+12) (rev32 ((s.gpr .r8).setWidth 32))).write
    (s.gpr .r14) 16 (rev128 (s.vpr .v10))

def exitState (s : State) : State :=
  ({(s.write .r11 12).writeV .v10 (VG.Proof.Aes.PPC64LE.Crypto.flip (s.vpr .v10)) with mem := exitMem s}).write .r12 (s.gpr .r16-128)

theorem exitCounter_ok (s : State) (hw : InRegions s.wr (s.gpr .r5+12) 4) :
    WP isa (.block [.li .r11 12,.storeRev .w .r8 .r5 .r11]) s
      (· = {s.write .r11 12 with mem := s.mem.writeW (s.gpr .r5+12) (rev32 ((s.gpr .r8).setWidth 32))}) := by
  have hw' : InRegions (s.write .r11 12).wr
      ((s.write .r11 12).gpr .r5+(s.write .r11 12).gpr .r11) 4 := by
    simpa only [RegUpd.wr_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true] using hw
  apply WP.of_runBlock
  rw [runBlock_cons,exec_li (imm := 12) (by decide),runStep_some]
  change ∃ t, runBlock isa [.storeRev .w .r8 .r5 .r11] (s.write .r11 12)=some t ∧ _
  rw [runBlock_cons,exec_storeRev_w (by decide) hw',runStep_some,runBlock_nil]
  simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,RegUpd.mem_write,
    Option.some.injEq,exists_eq_left']



theorem exitWrites_ok (s : State) (hz : s.gpr .r0=0)
    (hm : s.vpr .v19=Impl.Aes.PPC64LE.Crypto.byteMask)
    (hc : InRegions s.wr (s.gpr .r5+12) 4) (hy : InRegions s.wr (s.gpr .r14) 16) :
    WP isa (.block (([.li .r11 12,.storeRev .w .r8 .r5 .r11] : List Instr) ++
      Impl.Aes.PPC64LE.Crypto.store .v10 .r14 ++ ([.subi .r12 .r16 128] : List Instr))) s
      (· = exitState s) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (exitCounter_ok s hc) fun u hu => ?_
  subst u
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.PPC64LE.Crypto.store_ok .v10 .r14 _ (by decide)
    (by simpa only [RegUpd.gpr_write,reduceCtorEq,ite_false] using hz) hm hy) fun v hv => ?_
  subst v
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec_subi (n := .r16) (imm := 128) (by decide) (by decide),
    gpr_writeV,RegUpd.gpr_write,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl


theorem exitState_keep (s : State) : Keep [.r11,.r12] s (exitState s) := by
  refine ⟨?_,rfl,rfl⟩
  intro r hr
  have h11 : r≠.r11 := fun he => hr (by simp [he])
  have h12 : r≠.r12 := fun he => hr (by simp [he])
  simp only [exitState,RegUpd.gpr_write,h12,ite_false,gpr_writeV,h11]


theorem exitState_frame (s : State) :
    Frame [⟨s.gpr .r5,16⟩,⟨s.gpr .r14,16⟩] s.mem (exitState s).mem := by
  exact ((Frame.refl [⟨s.gpr .r5,16⟩,⟨s.gpr .r14,16⟩] s.mem).writeW (r := ⟨s.gpr .r5,16⟩) (by simp) (rev32 ((s.gpr .r8).setWidth 32))
    (Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide))).write
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (rev128 (s.vpr .v10)) (Region.contains_self _ _)


theorem saved_during_loop {base entry ready s : State} {n nr k : Nat}
    (lay : CoreLayout base n) (hc : CacheResult base entry nr ready)
    (hs : LoopInv base ready n nr k s) :
    Spill.Saved (base.gpr .r10) base.gpr Impl.AesGcm.PPC64LE.Blocks.saved s.mem := by
  have hsave := saved_after_body base hc.frame
  refine hsave.frame hs.frame fun p hp r hr => ?_
  have hb : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, p.2+8≤128 := by decide
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (Or.inl (hb p hp)) (by have := hb p hp; omega) (by decide)
  · rw [List.mem_singleton] at hr
    subst r
    exact ((lay.scratch (coreData base n) (by simp)).symm).sub_left
      (Offset.sub_base _ (d := p.2) (n := 8) (k := 2048) (by have := hb p hp; omega))


structure ExitResult (base start s : State) : Prop where
  keep : Keep ([.r11,.r12] ++ Impl.AesGcm.PPC64LE.Blocks.saved.map Prod.fst) start s
  restored : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, s.gpr p.1=base.gpr p.1
  mem : s.mem=exitMem start
  frame : Frame [coreCounter base,coreY base] start.mem s.mem


theorem exit_ok {base s : State} {n nr : Nat} (lay : CoreLayout base n)
    (fx : LoopFixed base nr s)
    (hsv : Spill.Saved (base.gpr .r10) base.gpr Impl.AesGcm.PPC64LE.Blocks.saved s.mem) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.exit) s (ExitResult base s) := by
  have hc : InRegions s.wr (s.gpr .r5+12) 4 := by
    rw [fx.wr,fx.counter]
    exact lay.writes _ _ ⟨coreCounter base,by simp,
      Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide)⟩
  have hy : InRegions s.wr (s.gpr .r14) 16 := by
    rw [fx.wr,fx.yPtr]
    exact lay.writes _ _ ⟨coreY base,by simp,Region.contains_self _ _⟩
  have hf : Frame [coreCounter base,coreY base] s.mem (exitState s).mem := by
    simpa only [fx.counter,fx.yPtr,coreCounter,coreY] using exitState_frame s
  have hsaved : Spill.Saved (base.gpr .r10) base.gpr Impl.AesGcm.PPC64LE.Blocks.saved (exitState s).mem := by
    refine hsv.frame hf fun p hp r hr => ?_
    have hb : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, p.2+8≤128 := by decide
    have hsub : Region.Sub ⟨base.gpr .r10+BitVec.ofNat 64 p.2,8⟩ (coreWork base) :=
      Offset.sub_base _ (by have := hb p hp; omega)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ((lay.scratch (coreCounter base) (by simp)).symm).sub_left hsub
    · rw [List.mem_singleton] at hr
      subst r
      exact ((lay.scratch (coreY base) (by simp)).symm).sub_left hsub
  have hb : (exitState s).gpr .r12=base.gpr .r10 := by
    rw [exitState,RegUpd.gpr_write_self,fx.table,BitVec.add_sub_cancel]
  have hread : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved,
      InRegions ((exitState s).rd++(exitState s).wr) (base.gpr .r10+BitVec.ofNat 64 p.2) 8 := by
    intro p hp
    have ho : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, p.2+8≤128 := by decide
    rw [(exitState_keep s).2.1,(exitState_keep s).2.2,fx.rd,fx.wr]
    obtain ⟨r,hr,hp⟩ := lay.work_write (offset := p.2) (len := 8) (by have := ho p hp; omega)
    exact ⟨r,List.mem_append_right _ hr,hp⟩
  change WP isa (.block ((([.li .r11 12,.storeRev .w .r8 .r5 .r11] : List Instr) ++
    Impl.Aes.PPC64LE.Crypto.store .v10 .r14 ++ ([.subi .r12 .r16 128] : List Instr)) ++
    Spill.restoreCode .r12 Impl.AesGcm.PPC64LE.Blocks.saved)) s _
  rw [WP.block_append_iff]
  refine WP.mono (exitWrites_ok s fx.zero fx.mask hc hy) fun t ht => ?_
  subst t
  refine WP.mono (Spill.restore_wp (by decide) hb
    (show ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, p.2%8=0 ∧ p.2<32768 from by decide)
    (by decide) hread hsaved) fun t ht => ?_
  refine ⟨?_,ht.gpr,ht.mem,?_⟩
  · exact (exitState_keep s).trans ⟨ht.other,ht.rd,ht.wr⟩
  · simpa only [ht.mem] using hf


theorem processed_ciphertext {base : State} {m : Mem} {n nr : Nat}
    (hp : VG.Proof.Aes.Memory.Processed base.mem m (base.gpr .r6) n n (cipherState base nr)) :
    Spec.Gcm.blocksAt m (base.gpr .r6) n=Spec.Gcm.ctr32
      (Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr) (Spec.Gcm.blockAt base.mem (base.gpr .r5))
      (Spec.Gcm.blocksAt base.mem (base.gpr .r6) n) := by
  apply VG.Proof.Aes.PPC64LE.Crypto.ctr_processed
  have he : cipherState base nr=VG.Proof.Aes.PPC64LE.Crypto.outputState false true nr
      (cachedSchedule base nr) (Spec.Gcm.blockAt base.mem (base.gpr .r5)) base.mem (base.gpr .r6) := by
    funext i
    simp only [cipherState,cipherBlock,Spec.Gcm.ctxCiph,cachedSchedule,
      VG.Proof.Aes.PPC64LE.Crypto.outputState,ite_true,BitVec.xor_comm]
  simpa only [he,cachedSchedule] using hp


theorem exitCounter_value {base s : State} {n nr : Nat} (lay : CoreLayout base n)
    (fx : LoopFixed base nr s)
    (hf : Frame [coreWork base,coreData base n] base.mem s.mem)
    (hw : (s.gpr .r8).setWidth 32=(Nat.repeat Spec.Gcm.inc32 n
      (Spec.Gcm.blockAt base.mem (base.gpr .r5))).extractLsb' 0 32) :
    Spec.Gcm.blockAt (exitMem s) (base.gpr .r5)=
      Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt base.mem (base.gpr .r5)) := by
  apply VG.Proof.Aes.PPC64LE.Crypto.counter_after (word := (s.gpr .r8).setWidth 32)
  · rw [hw,counterValue]
    exact BitVec.extractLsb'_append_eq_right
  · intro i hi
    have hyoutside : ¬ ((base.gpr .r5+BitVec.ofNat 64 i)-s.gpr .r14).toNat<16 := by
      intro h
      apply lay.counterY (base.gpr .r5+BitVec.ofNat 64 i)
        (Offset.contains_base _ (d := i) (n := 1) (k := 16) (by omega) (by omega))
      change ((base.gpr .r5+BitVec.ofNat 64 i)-base.gpr .r9).toNat+1≤16
      rw [fx.yPtr] at h
      omega
    change (exitMem s) (base.gpr .r5+BitVec.ofNat 64 i)=_
    rw [exitMem,fx.counter,Mem.write_apply hyoutside]
    change (s.mem.write (base.gpr .r5+12) 4 (rev32 ((s.gpr .r8).setWidth 32))) (base.gpr .r5+BitVec.ofNat 64 i)=_
    rw [Mem.write,show (12 : BitVec 64)=BitVec.ofNat 64 12 from rfl,
      Offset.sub_toNat' (base.gpr .r5) (by omega) (by omega)]
    by_cases hil : i<12
    · rw [ite_eq_right (show ¬12≤i by omega),ite_eq_right (show ¬2^64+i-12<4 by omega),ite_eq_left hil]
      exact hf.bytes (R := coreCounter base) (by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact lay.scratch (coreCounter base) (by simp)
        · rw [List.mem_singleton] at hr
          subst r
          exact lay.data (coreCounter base) (by simp)) (by change 16≤2^64; decide) hi
    · rw [ite_eq_left (show 12≤i by omega),ite_eq_left (show i-12<4 by omega),ite_eq_right hil]


theorem processed_blocks {base : State} {m : Mem} {n nr : Nat}
    (hp : VG.Proof.Aes.Memory.Processed base.mem m (base.gpr .r6) n n (cipherState base nr)) :
    Spec.Gcm.blocksAt m (base.gpr .r6) n=(List.range n).map (cipherBlock base nr) := by
  apply List.map_congr_left
  intro i hi
  apply VG.Proof.Aes.PPC64LE.Crypto.aesState_inj
  rw [VG.Proof.Aes.PPC64LE.Crypto.aesState_blockAt]
  exact hp.stateAt (List.mem_range.mp hi) (Nat.le_refl _)


structure CoreResult (base : State) (n nr : Nat) (s : State) : Prop where
  frame : Frame [coreWork base,coreData base n,coreCounter base,coreY base] base.mem s.mem
  ciphertext : Spec.Gcm.blocksAt s.mem (base.gpr .r6) n=Spec.Gcm.ctr32
    (Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr) (Spec.Gcm.blockAt base.mem (base.gpr .r5))
    (Spec.Gcm.blocksAt base.mem (base.gpr .r6) n)
  counter : Spec.Gcm.blockAt s.mem (base.gpr .r5)=
    Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt base.mem (base.gpr .r5))
  y : Spec.Gcm.blockAt s.mem (base.gpr .r9)=Spec.Gcm.ghashFrom
    (Spec.Gcm.ctxH base.mem (base.gpr .r3)) (Spec.Gcm.blockAt base.mem (base.gpr .r9))
    (Spec.Gcm.blocksAt s.mem (base.gpr .r6) n)
  restored : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.saved, s.gpr p.1=base.gpr p.1


theorem finish_ok {base entry ready s : State} {n nr : Nat} (lay : CoreLayout base n)
    (hc : CacheResult base entry nr ready) (hs : LoopInv base ready n nr n s) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.exit) s (CoreResult base n nr) := by
  have hfready : Frame [coreWork base] base.mem ready.mem :=
    lay.saved_frame.trans (coreBody_frame hc.frame)
  have hfloop : Frame [coreWork base,coreData base n] ready.mem s.mem := hs.frame.sub (fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨coreWork base,by simp,coreBody_sub base⟩
    · rw [List.mem_singleton] at hr
      subst r
      exact ⟨coreData base n,by simp,fun _ h => h⟩)
  have hfbase := (hfready.mono (by simp)).trans hfloop
  refine WP.mono (exit_ok lay hs.fixed (saved_during_loop lay hc hs)) fun t ht => ?_
  have hp := hs.processed.frame ht.frame (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (lay.data (coreCounter base) (by simp)).symm
    · rw [List.mem_singleton] at hr
      subst r
      exact (lay.data (coreY base) (by simp)).symm) lay.size
  refine ⟨(hfbase.mono (by simp)).trans (ht.frame.mono (by simp)),processed_ciphertext hp,?_,?_,ht.restored⟩
  · rw [ht.mem]
    exact exitCounter_value lay hs.fixed hfbase hs.word
  · rw [processed_blocks hp]
    change Spec.Gcm.blockAt t.mem (base.gpr .r9)=hashPrefix base nr n
    rw [ht.mem,exitMem,← hs.fixed.yPtr,← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt]
    change rev128 (((s.mem.writeW (s.gpr .r5+12) (rev32 ((s.gpr .r8).setWidth 32))).writeW
      (s.gpr .r14) (rev128 (s.vpr .v10))).readW (s.gpr .r14) 128)=_
    rw [Mem.readW_writeW_self _ _ 16 _ (by decide),rev128_rev128,hs.y]


theorem core_nonempty_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (base : State) (n nr : Nat) (lay : CoreLayout base n) (hn : base.gpr .r7=BitVec.ofNat 64 n)
    (hpos : 0<n) (hm : n%8=0) (hmin : 9<nr) (hmax : nr<15)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr) (hH : base.gpr .r8=base.gpr .r3+240#64) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.code base (CoreResult base n nr) := by
  have hne : base.gpr .r7≠0 := by
    intro he
    have hh := congrArg BitVec.toNat he
    rw [hn,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := lay.size; omega)] at hh
    exact Nat.ne_of_gt hpos hh
  rw [Impl.AesGcm.PPC64LE.Blocks.code]
  refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
    Option.some.injEq,beq_eq_false_iff_ne] using hne) (by simp) (fun _ => ?_)
  apply WP.seq
  refine WP.mono (entry_ok base n lay hH) fun entry he => ?_
  apply WP.seq
  refine WP.mono (cache_ok base entry n nr lay he hmax hr) fun ready hc => ?_
  have hi := LoopInv.initial lay hc hn
  apply WP.seq
  refine WP.mono (batches_ok lay hmin hmax (by omega) (by simpa only [Nat.sub_zero] using hm) hi)
    fun t ht => finish_ok lay hc ht


def coreVolatile : List Reg := [.r0,.r3,.r4,.r5,.r6,.r7,.r8,.r9,.r10,.r11,.r12]

theorem core_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (base : State) (n nr : Nat) (lay : CoreLayout base n) (hn : base.gpr .r7=BitVec.ofNat 64 n)
    (hm : n%8=0) (hmin : 9<nr) (hmax : nr<15)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr) (hH : base.gpr .r8=base.gpr .r3+240#64) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.code base fun t => CoreResult base n nr t ∧ Keep coreVolatile base t := by
  have hfunc : WP isa Impl.AesGcm.PPC64LE.Blocks.code base (CoreResult base n nr) := by
    by_cases hz : n=0
    · subst n
      rw [Impl.AesGcm.PPC64LE.Blocks.code]
      refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hn]; rfl)
        (fun _ => WP.block_nil ?_) (by simp)
      refine ⟨Frame.refl _ _,?_,rfl,?_,fun _ _ => rfl⟩
      · simp only [Spec.Gcm.blocksAt,List.range_zero,List.map_nil,Spec.Gcm.ctr32,Spec.Gcm.keystream,
          List.length_nil,List.zipWith_nil_left]
      · rfl
    · exact core_nonempty_ok base n nr lay hn (by omega) hm hmin hmax hr hH
  refine WP.mono (WP.keep (coreVolatile++Impl.AesGcm.PPC64LE.Blocks.saved.map Prod.fst) hfunc
    (by lit_decide) (by lit_decide)) fun t ⟨ht,hk⟩ => ⟨ht,?_,hk.2⟩
  intro r hr
  by_cases hs : r ∈ Impl.AesGcm.PPC64LE.Blocks.saved.map Prod.fst
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hs
    exact ht.restored p hp
  · exact hk.gpr (by simpa only [List.mem_append,not_or] using And.intro hr hs)


def wrapperConfigState (s : State) : State :=
  (((((((s.write .r29 (s.gpr .r3)).write .r28 (s.gpr .r4)).write .r27 (s.gpr .r5)).write
    .r26 (s.gpr .r6)).write .r30 (s.gpr .r7)).write .r25 (s.gpr .r8)).write
    .r31 (s.gpr .r9)).write .r12 (s.gpr .r8 >>> 5)

theorem wrapperConfig_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.wrapperConfig) s (· = wrapperConfigState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.wrapperConfig,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,exec_lsr_d (sh := 5) (by decide),
    RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,Option.some.injEq,exists_eq_left']
  rfl


theorem wrapperSaveLR_ok (s : State) (hw : InRegions s.wr (s.gpr .r9+56) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.wrapperSaveLR) s
      (· = {s.write .r0 s.lr with mem := s.mem.writeW (s.gpr .r9+56) s.lr}) := by
  have hw' : InRegions (s.write .r0 s.lr).wr ((s.write .r0 s.lr).gpr .r9+56) 8 := hw
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.wrapperSaveLR,runBlock_cons,runStep_some,runBlock_nil,exec_mflr,
    exec_store_d (by decide) ⟨by decide,by decide⟩ hw',RegUpd.gpr_write,
    reduceCtorEq,ite_true,ite_false,RegUpd.mem_write,Option.some.injEq,exists_eq_left']
  rfl


def wrapperHeaderMem (s : State) : Mem :=
  (Spill.saveMem s.mem (s.gpr .r9) s.gpr Impl.AesGcm.PPC64LE.Blocks.wrapperSaved).writeW (s.gpr .r9+56) s.lr

def wrapperEntryState (s : State) : State :=
  wrapperConfigState {s.write .r0 s.lr with mem := wrapperHeaderMem s}

theorem wrapperEntry_ok (s : State)
    (hw : ∀ off, off+8≤64 → InRegions s.wr (s.gpr .r9+BitVec.ofNat 64 off) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.wrapperEntry) s (· = wrapperEntryState s) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.wrapperEntry,WP.block_append_iff,WP.block_append_iff]
  have hs : WP isa (.block (Spill.saveCode .r9 Impl.AesGcm.PPC64LE.Blocks.wrapperSaved)) s
      (· = {s with mem := Spill.saveMem s.mem (s.gpr .r9) s.gpr Impl.AesGcm.PPC64LE.Blocks.wrapperSaved}) := by
    rw [← List.append_nil (Spill.saveCode .r9 Impl.AesGcm.PPC64LE.Blocks.wrapperSaved)]
    apply Spill.save_ok (by decide)
      (show ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved, p.2%8=0 ∧ p.2<32768 from by decide)
    · intro p hp
      have hh : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved, p.2+8≤64 := by decide
      exact hw _ (hh p hp)
    · exact WP.block_nil rfl
  refine WP.mono hs fun saved hs => ?_
  subst saved
  refine WP.mono (wrapperSaveLR_ok _ (hw 56 (by decide))) fun linked hl => ?_
  subst linked
  exact wrapperConfig_ok _


def bulkArgsState (s : State) : State :=
  (((((((((s.write .r3 (s.gpr .r29)).write .r4 (s.gpr .r28)).write .r5 (s.gpr .r27)).write
    .r6 (s.gpr .r30)).write .r0 7).write .r11 (s.gpr .r25 &&& 7)).write
    .r7 (s.gpr .r25-(s.gpr .r25 &&& 7))).write .r8 (s.gpr .r29+240)).write
    .r9 (s.gpr .r26)).write .r10 (s.gpr .r31+64)

theorem bulkArgs_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.bulkArgs) s (· = bulkArgsState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.bulkArgs,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,exec_li (imm := 7) (by decide),exec_sub,
    exec_addi (n := .r29) (imm := 240) (by decide) (by decide),
    exec_addi (n := .r31) (imm := 64) (by decide) (by decide),
    RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,Option.some.injEq,exists_eq_left']
  rfl


theorem mask_tail (n : Nat) : BitVec.ofNat 64 n &&& 7=BitVec.ofNat 64 (n%8) := by
  change BitVec.ofNat 64 n &&& BitVec.ofNat 64 (2^3-1)=_
  rw [← BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod]


def bulkRestState (s : State) : State :=
  (((((s.write .r0 7).write .r11 (s.gpr .r25 &&& 7)).write
    .r12 (s.gpr .r25-(s.gpr .r25 &&& 7))).write
    .r12 ((s.gpr .r25-(s.gpr .r25 &&& 7)) <<< 4)).write
    .r30 (s.gpr .r30+((s.gpr .r25-(s.gpr .r25 &&& 7)) <<< 4))).write .r25 (s.gpr .r25 &&& 7)

theorem bulkRest_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.bulkRest) s (· = bulkRestState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.bulkRest,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,exec_li (imm := 7) (by decide),
    exec_sub,exec_lsl (sh := 4) (by decide),exec_add,
    RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,Option.some.injEq,exists_eq_left']
  rfl


theorem wrapperHeader_frame (s : State) :
    Frame [⟨s.gpr .r9,64⟩] s.mem (wrapperHeaderMem s) := by
  have hf := Spill.saveMem_frame_base
    (show ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved, p.2+8≤64 from by decide)
    (by decide) s.mem (s.gpr .r9) s.gpr
  exact hf.writeW (List.mem_singleton_self _) s.lr
    (Offset.contains_base _ (d := 56) (n := 8) (k := 64) (by decide) (by decide))


theorem wrapperHeader_saved (s : State) :
    Spill.Saved (s.gpr .r9) s.gpr Impl.AesGcm.PPC64LE.Blocks.wrapperSaved (wrapperHeaderMem s) := by
  have hs := Spill.saveMem_saved (show Spill.Fits Impl.AesGcm.PPC64LE.Blocks.wrapperSaved from by decide)
    s.mem (s.gpr .r9) s.gpr
  have hf : Frame [⟨s.gpr .r9+56,8⟩]
      (Spill.saveMem s.mem (s.gpr .r9) s.gpr Impl.AesGcm.PPC64LE.Blocks.wrapperSaved) (wrapperHeaderMem s) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) s.lr (Region.contains_self _ _)
  refine hs.frame hf fun p hp r hr => ?_
  rw [List.mem_singleton] at hr
  subst r
  have ho : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved, p.2+8≤56 := by decide
  exact Offset.disjoint _ (Or.inl (ho p hp)) (by have := ho p hp; omega) (by decide)


theorem wrapperHeader_lr (s : State) : (wrapperHeaderMem s).readW (s.gpr .r9+56) 64=s.lr :=
  Mem.readW_writeW_self64 ..


structure WrapperFixed (base s : State) : Prop where
  rd : s.rd=base.rd
  wr : s.wr=base.wr
  ctx : s.gpr .r29=base.gpr .r3
  rounds : s.gpr .r28=base.gpr .r4
  counter : s.gpr .r27=base.gpr .r5
  y : s.gpr .r26=base.gpr .r6
  work : s.gpr .r31=base.gpr .r9


theorem wrapperEntry_fixed (s : State) : WrapperFixed s (wrapperEntryState s) := by
  constructor <;>
    simp only [wrapperEntryState,wrapperConfigState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false,
      RegUpd.rd_write,RegUpd.wr_write]


theorem WrapperFixed.keep {base s t : State} (hf : WrapperFixed base s)
    (hk : Keep coreVolatile s t) : WrapperFixed base t :=
  ⟨hk.2.1.trans hf.rd,hk.2.2.trans hf.wr,
    (hk.gpr (by decide)).trans hf.ctx,(hk.gpr (by decide)).trans hf.rounds,
    (hk.gpr (by decide)).trans hf.counter,(hk.gpr (by decide)).trans hf.y,(hk.gpr (by decide)).trans hf.work⟩


theorem bulkArgs_keep (s : State) : Keep coreVolatile s (bulkArgsState s) := by
  refine ⟨?_,rfl,rfl⟩
  intro r hr
  have hnot : ∀ q ∈ coreVolatile, r≠q := fun q hq he => hr (he ▸ hq)
  simp only [bulkArgsState,RegUpd.gpr_write,hnot .r3 (by decide),hnot .r4 (by decide),
    hnot .r5 (by decide),hnot .r6 (by decide),hnot .r0 (by decide),hnot .r11 (by decide),
    hnot .r7 (by decide),hnot .r8 (by decide),hnot .r9 (by decide),hnot .r10 (by decide),ite_false]



structure BulkArgsResult (base start s : State) (n : Nat) : Prop where
  fixed : WrapperFixed base s
  mem : s.mem=start.mem
  ctx : s.gpr .r3=base.gpr .r3
  rounds : s.gpr .r4=base.gpr .r4
  counter : s.gpr .r5=base.gpr .r5
  data : s.gpr .r6=start.gpr .r30
  left : s.gpr .r7=BitVec.ofNat 64 (n-n%8)
  h : s.gpr .r8=base.gpr .r3+240
  y : s.gpr .r9=base.gpr .r6
  work : s.gpr .r10=base.gpr .r9+64


theorem bulkArgs_result {base s : State} {n : Nat} (hf : WrapperFixed base s)
    (hn : s.gpr .r25=BitVec.ofNat 64 n) :
    BulkArgsResult base s (bulkArgsState s) n := by
  refine ⟨hf.keep (bulkArgs_keep s),rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [bulkArgsState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false]
  · exact hf.ctx
  · exact hf.rounds
  · exact hf.counter
  · rw [hn,mask_tail,Offset.ofNat_sub_ofNat (Nat.mod_le _ _)]
  · rw [hf.ctx]
  · exact hf.y
  · rw [hf.work]


def wrapperExitState (s : State) : State :=
  {s.write .r0 (s.mem.readW (s.gpr .r31+56) 64) with lr := s.mem.readW (s.gpr .r31+56) 64}.write
    .r12 (s.gpr .r31)

theorem wrapperExitRead_ok (s : State) (hr : InRegions (s.rd++s.wr) (s.gpr .r31+56) 8) :
    WP isa (.block [.load .d .r0 .r31 56,.mtlr .r0,Impl.Aes.PPC64LE.Crypto.mov .r12 .r31]) s
      (· = wrapperExitState s) := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.mov,runBlock_cons,runStep_some,runBlock_nil,
    exec_load_d (by decide) ⟨by decide,by decide⟩ hr,exec_mtlr,exec_logic,BitVec.or_self,
    RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  rfl


structure WrapperExitResult (base start s : State) : Prop where
  restored : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved, s.gpr p.1=base.gpr p.1
  other : ∀ r, r ∉ (.r0 :: .r12 :: Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst) → s.gpr r=start.gpr r
  mem : s.mem=start.mem
  rd : s.rd=start.rd
  wr : s.wr=start.wr
  lr : s.lr=base.lr
  sp : s.sp=start.sp


theorem wrapperExit_ok (base s : State) (hwork : s.gpr .r31=base.gpr .r9)
    (hsv : Spill.Saved (base.gpr .r9) base.gpr Impl.AesGcm.PPC64LE.Blocks.wrapperSaved s.mem)
    (hlr : s.mem.readW (base.gpr .r9+56) 64=base.lr)
    (hr : ∀ off, off+8≤64 → InRegions (s.rd++s.wr) (base.gpr .r9+BitVec.ofNat 64 off) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.wrapperExit) s (WrapperExitResult base s) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.wrapperExit,WP.block_append_iff]
  refine WP.mono (wrapperExitRead_ok s (by rw [hwork]; exact hr 56 (by decide))) fun u hu => ?_
  subst u
  have hb : (wrapperExitState s).gpr .r12=base.gpr .r9 := (RegUpd.gpr_write_self ..).trans hwork
  have hslots : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved,
      InRegions ((wrapperExitState s).rd++(wrapperExitState s).wr) (base.gpr .r9+BitVec.ofNat 64 p.2) 8 := by
    intro p hp
    have ho : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved, p.2+8≤64 := by decide
    exact hr _ (ho p hp)
  change WP isa (.block (Spill.restoreCode .r12 Impl.AesGcm.PPC64LE.Blocks.wrapperSaved)) _ _
  refine WP.mono (Spill.restore_wp (by decide) hb
    (show ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved, p.2%8=0 ∧ p.2<32768 from by decide)
    (by decide) hslots hsv) fun t ht => ?_
  refine ⟨ht.gpr,?_,ht.mem,ht.rd,ht.wr,?_,ht.sp⟩
  · intro r hn
    have h0 : r≠.r0 := fun he => hn (by simp [he])
    have h12 : r≠.r12 := fun he => hn (by simp [he])
    have hsave : r ∉ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst := fun he => hn (by simp [he])
    rw [ht.other r hsave]
    simp only [wrapperExitState,RegUpd.gpr_write,h12,h0,ite_false]
  · rw [ht.lr]
    simpa only [wrapperExitState,RegUpd.lr_write,hwork] using hlr


def tailCtrState (s : State) : State :=
  (((((s.write .r3 (s.gpr .r29)).write .r4 (s.gpr .r28)).write .r5 (s.gpr .r27)).write
    .r6 (s.gpr .r30)).write .r7 (s.gpr .r25)).write .r8 (s.gpr .r31+64)

theorem tailCtrArgs_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.tailCtrArgs) s (· = tailCtrState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.tailCtrArgs,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    exec_addi (n := .r31) (imm := 64) (by decide) (by decide),
    RegUpd.gpr_write,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl


def tailGhState (s : State) : State :=
  ((((s.write .r3 (s.gpr .r29+240)).write .r4 (s.gpr .r26)).write
    .r5 (s.gpr .r30)).write .r6 (s.gpr .r25)).write .r7 (s.gpr .r31+64)

theorem tailGhArgs_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.tailGhArgs) s (· = tailGhState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.Blocks.tailGhArgs,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    exec_addi (n := .r29) (imm := 240) (by decide) (by decide),
    exec_addi (n := .r31) (imm := 64) (by decide) (by decide),
    RegUpd.gpr_write,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl


def tailBase (s : State) : State := (bulkArgsState s).write .r7 (s.gpr .r25)

structure TailConfig (s : State) (n nr : Nat) : Prop where
  layout : CoreLayout (tailBase s) n
  count : s.gpr .r25=BitVec.ofNat 64 n
  rounds : s.gpr .r28=BitVec.ofNat 64 nr
  valid : nr=10 ∨ nr=12 ∨ nr=14
  fit : (s.gpr .r30).toNat+16*n≤2^64


theorem tailCtr_keep (s : State) : Keep coreVolatile s (tailCtrState s) := by
  obtain ⟨_,_,_,he,hk⟩ := WP.keep coreVolatile (tailCtrArgs_ok s) (by lit_decide) (by lit_decide)
  subst he
  exact hk


theorem tailGh_keep (s : State) : Keep coreVolatile s (tailGhState s) := by
  obtain ⟨_,_,_,he,hk⟩ := WP.keep coreVolatile (tailGhArgs_ok s) (by lit_decide) (by lit_decide)
  subst he
  exact hk


private theorem TailConfig.ctr {s : State} {n nr : Nat} (hc : TailConfig s n nr) :
    VG.Proof.AesGcm.PPC64LE.CtrCall (tailCtrState s) (s.gpr .r29) (s.gpr .r27)
      (s.gpr .r30) (s.gpr .r31+64) nr n := by
  have lay := hc.layout
  have hkey : Region.Sub (⟨s.gpr .r29,240⟩ : Region) (coreKey (tailBase s)) :=
    Region.sub_prefix (by decide)
  have hread : Covers ([⟨s.gpr .r29,240⟩] ++
      [⟨s.gpr .r27,16⟩,⟨s.gpr .r30,16*n⟩,⟨s.gpr .r31+64,2048⟩]) (s.rd++s.wr) := by
    intro p len hp
    obtain ⟨r,hr,hpr⟩ := hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · apply lay.reads p len
      refine ⟨coreKey (tailBase s),by simp,?_⟩
      change (p-s.gpr .r29).toNat+len≤256
      change (p-s.gpr .r29).toNat+len≤240 at hpr
      omega
    all_goals
      obtain ⟨r,hr,hpr⟩ := lay.writes p len (by
        first | exact ⟨coreCounter (tailBase s),by simp,hpr⟩
              | exact ⟨coreData (tailBase s) n,by simp,hpr⟩
              | exact ⟨coreWork (tailBase s),by simp,hpr⟩)
      exact ⟨r,List.mem_append_right _ hr,hpr⟩
  have hwrite : Covers [⟨s.gpr .r27,16⟩,⟨s.gpr .r30,16*n⟩,⟨s.gpr .r31+64,2048⟩] s.wr := by
    intro p len ⟨r,hr,hp⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals apply lay.writes p len
    · exact ⟨coreCounter (tailBase s),by simp,hp⟩
    · exact ⟨coreData (tailBase s) n,by simp,hp⟩
    · exact ⟨coreWork (tailBase s),by simp,hp⟩
  refine ⟨?_,?_,?_,?_,?_,?_,hc.valid,by have := lay.size; omega,
    lay.counterKey.sub_left hkey,(lay.data (coreKey (tailBase s)) (by simp)).sub_left hkey,
    (lay.scratch (coreKey (tailBase s)) (by simp)).sub_left hkey,
    lay.data (coreCounter (tailBase s)) (by simp),lay.scratch (coreCounter (tailBase s)) (by simp),
    lay.scratch (coreData (tailBase s) n) (by simp),hc.fit,hread,hwrite⟩
  all_goals simp only [tailCtrState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false]
  · exact hc.rounds
  · exact hc.count


private theorem TailConfig.gh {s u : State} {n nr : Nat} (hc : TailConfig s n nr)
    (hu : VG.Proof.AesGcm.PPC64LE.CtrPost (tailCtrState s) (s.gpr .r29) (s.gpr .r27)
      (s.gpr .r30) (s.gpr .r31+64) nr n u) :
    VG.Proof.AesGcm.PPC64LE.GhCall (tailGhState u) (s.gpr .r29+240) (s.gpr .r26)
      (s.gpr .r30) (s.gpr .r31+64) n := by
  have lay := hc.layout
  have hp : ∀ r ∈ preserved, u.gpr r=s.gpr r := fun r hr =>
    (hu.saved r hr).trans ((tailCtr_keep s).gpr (by
      have hdis : ∀ r ∈ preserved, r ∉ coreVolatile := by decide
      exact hdis r hr))
  have hr : (tailGhState u).rd++(tailGhState u).wr=s.rd++s.wr := by
    rw [(tailGh_keep u).2.1,(tailGh_keep u).2.2,hu.rd,hu.wr]
    rfl
  have hw : (tailGhState u).wr=s.wr := by
    rw [(tailGh_keep u).2.2,hu.wr]
    rfl
  have hwrites : Covers [⟨s.gpr .r26,16⟩,⟨s.gpr .r31+64,256⟩] (tailGhState u).wr := by
    rw [hw]
    apply Covers.trans ?_ lay.writes
    apply Covers.of_sub
    intro r h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨coreY (tailBase s),by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤16; decide⟩
    · rw [List.mem_singleton] at h
      subst r
      exact ⟨coreWork (tailBase s),by simp,0,by exact (BitVec.add_zero _).symm,by change 0+256≤2048; decide⟩
  have hreads : Covers ([⟨s.gpr .r29+240,16⟩,⟨s.gpr .r30,16*n⟩] ++
      [⟨s.gpr .r26,16⟩,⟨s.gpr .r31+64,256⟩]) ((tailGhState u).rd++(tailGhState u).wr) := by
    rw [hr]
    have hall := Covers.append_left lay.reads (Covers.right lay.writes)
    apply Covers.trans ?_ hall
    apply Covers.of_sub
    intro r h
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with (rfl | rfl) | rfl | rfl
    · exact ⟨coreKey (tailBase s),by simp,240,rfl,by change 240+16≤256; decide⟩
    · exact ⟨coreData (tailBase s) n,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16*n≤16*n; omega⟩
    · exact ⟨coreY (tailBase s),by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤16; decide⟩
    · exact ⟨coreWork (tailBase s),by simp,0,by exact (BitVec.add_zero _).symm,by change 0+256≤2048; decide⟩
  have hh : Region.Sub (⟨s.gpr .r29+240,16⟩ : Region) (coreKey (tailBase s)) :=
    Offset.sub_base _ (d := 240) (n := 16) (k := 256) (by decide)
  have hs : Region.Sub (⟨s.gpr .r31+64,256⟩ : Region) (coreWork (tailBase s)) := Region.sub_prefix (by decide)
  refine ⟨?_,?_,?_,?_,?_,by have := lay.size; omega,
    lay.yKey.sub_left hh,(lay.scratch (coreKey (tailBase s)) (by simp)).sub_left hh |>.sub_right hs,
    lay.data (coreY (tailBase s)) (by simp),(lay.scratch (coreY (tailBase s)) (by simp)).sub_right hs,
    (lay.scratch (coreData (tailBase s) n) (by simp)).sub_right hs,hreads,hwrites⟩
  all_goals simp only [tailGhState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false]
  · rw [hp .r29 (by decide)]
  · exact hp .r26 (by decide)
  · exact hp .r30 (by decide)
  · rw [hp .r25 (by decide),hc.count]
  · rw [hp .r31 (by decide)]


theorem block_frame {m m' : Mem} {rs : List Region} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p,16⟩ : Region).Disjoint r) : Spec.Gcm.blockAt m' p=Spec.Gcm.blockAt m p := by
  rw [← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,
    hf.read (Region.contains_self _ _) hd (by decide)]


theorem blocks_frame {m m' : Mem} {rs : List Region} {p : Addr} {n : Nat} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p,16*n⟩ : Region).Disjoint r) :
    Spec.Gcm.blocksAt m' p n=Spec.Gcm.blocksAt m p n := by
  apply List.map_congr_left
  intro i hi
  exact block_frame hf fun r hr => (hd r hr).sub_left
    (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*n) (by have := List.mem_range.mp hi; omega))


structure TailResult (base : State) (n nr : Nat) (s : State) : Prop where
  rd : s.rd=base.rd
  wr : s.wr=base.wr
  sp : s.sp=base.sp
  saved : ∀ r ∈ preserved, s.gpr r=base.gpr r
  frame : Frame [coreCounter (tailBase base),coreY (tailBase base),coreData (tailBase base) n,
    coreWork (tailBase base)] base.mem s.mem
  ciphertext : Spec.Gcm.blocksAt s.mem (base.gpr .r30) n=Spec.Gcm.ctr32
    (Spec.Gcm.ctxCiph base.mem (base.gpr .r29) nr) (Spec.Gcm.blockAt base.mem (base.gpr .r27))
    (Spec.Gcm.blocksAt base.mem (base.gpr .r30) n)
  counter : Spec.Gcm.blockAt s.mem (base.gpr .r27)=
    Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt base.mem (base.gpr .r27))
  y : Spec.Gcm.blockAt s.mem (base.gpr .r26)=Spec.Gcm.ghashFrom
    (Spec.Gcm.ctxH base.mem (base.gpr .r29)) (Spec.Gcm.blockAt base.mem (base.gpr .r26))
    (Spec.Gcm.blocksAt s.mem (base.gpr .r30) n)


theorem tail_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (n nr : Nat) (hc : TailConfig s n nr) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.tail s (TailResult s n nr) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.tail]
  by_cases hz : n=0
  · subst n
    refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hc.count]; rfl)
      (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨rfl,rfl,rfl,fun _ _ => rfl,Frame.refl _ _,?_,rfl,?_⟩
    · simp only [Spec.Gcm.blocksAt,List.range_zero,List.map_nil,Spec.Gcm.ctr32,Spec.Gcm.keystream,
        List.length_nil,List.zipWith_nil_left]
    · rfl
  · have hne : s.gpr .r25≠0 := by
      intro he
      have hh := congrArg BitVec.toNat he
      rw [hc.count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := hc.layout.size; omega)] at hh
      exact hz hh
    refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
      Option.some.injEq,beq_eq_false_iff_ne] using hne) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (tailCtrArgs_ok s) fun ctr hcargs => ?_
    subst ctr
    apply WP.seq
    refine WP.mono (VG.Proof.AesGcm.PPC64LE.ctr_call hc.ctr) fun u hu => ?_
    apply WP.seq
    refine WP.mono (tailGhArgs_ok u) fun gh hgargs => ?_
    subst gh
    refine WP.mono (VG.Proof.AesGcm.PPC64LE.gh_call (hc.gh hu)) fun t ht => ?_
    have lay := hc.layout
    have hsp : ∀ r ∈ preserved, r ∉ coreVolatile := by decide
    have hp : ∀ r ∈ preserved, t.gpr r=s.gpr r := fun r hr =>
      (ht.saved r hr).trans (((tailGh_keep u).gpr (hsp r hr)).trans
        ((hu.saved r hr).trans ((tailCtr_keep s).gpr (hsp r hr))))
    have hfc : Frame [coreCounter (tailBase s),coreData (tailBase s) n,coreWork (tailBase s)] s.mem u.mem := hu.frame
    have hdata : Spec.Gcm.blocksAt t.mem (s.gpr .r30) n=Spec.Gcm.blocksAt u.mem (s.gpr .r30) n := by
      apply blocks_frame ht.frame
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (lay.data (coreY (tailBase s)) (by simp)).symm
      · rw [List.mem_singleton] at hr
        subst r
        exact (lay.scratch (coreData (tailBase s) n) (by simp)).sub_right (Region.sub_prefix (by decide))
    have hcounter : Spec.Gcm.blockAt t.mem (s.gpr .r27)=Spec.Gcm.blockAt u.mem (s.gpr .r27) := by
      apply block_frame ht.frame
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact lay.counterY
      · rw [List.mem_singleton] at hr
        subst r
        exact (lay.scratch (coreCounter (tailBase s)) (by simp)).sub_right (Region.sub_prefix (by decide))
    have hy : Spec.Gcm.blockAt u.mem (s.gpr .r26)=Spec.Gcm.blockAt s.mem (s.gpr .r26) := by
      apply block_frame hfc
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact lay.counterY.symm
      · exact lay.data (coreY (tailBase s)) (by simp)
      · exact lay.scratch (coreY (tailBase s)) (by simp)
    have hh : Spec.Gcm.blockAt u.mem (s.gpr .r29+240)=Spec.Gcm.ctxH s.mem (s.gpr .r29) := by
      apply block_frame hfc
      intro r hr
      have hsub : Region.Sub (⟨s.gpr .r29+240,16⟩ : Region) (coreKey (tailBase s)) :=
        Offset.sub_base _ (d := 240) (n := 16) (k := 256) (by decide)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact lay.counterKey.sub_left hsub
      · exact (lay.data (coreKey (tailBase s)) (by simp)).sub_left hsub
      · exact (lay.scratch (coreKey (tailBase s)) (by simp)).sub_left hsub
    have hfg : Frame [coreCounter (tailBase s),coreY (tailBase s),coreData (tailBase s) n,
        coreWork (tailBase s)] u.mem t.mem := ht.frame.sub (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨coreY (tailBase s),by simp,fun _ h => h⟩
      · rw [List.mem_singleton] at hr
        subst r
        exact ⟨coreWork (tailBase s),by simp,Region.sub_prefix (by decide)⟩)
    refine ⟨ht.rd.trans hu.rd,ht.wr.trans hu.wr,ht.sp.trans hu.sp,hp,
      (hfc.mono (by simp)).trans hfg,hdata.trans hu.out,hcounter.trans hu.ctr,?_⟩
    have hout : Spec.Gcm.blockAt t.mem (s.gpr .r26)=Spec.Gcm.ghashFrom
        (Spec.Gcm.blockAt u.mem (s.gpr .r29+240)) (Spec.Gcm.blockAt u.mem (s.gpr .r26))
        (Spec.Gcm.blocksAt u.mem (s.gpr .r30) n) := ht.out
    simpa only [hdata,hh,hy] using hout


theorem CoreLayout.prefix {s : State} {n k : Nat} (lay : CoreLayout s n) (hk : k≤n) : CoreLayout s k := by
  have hsub : Region.Sub (coreData s k) (coreData s n) := Region.sub_prefix (by change 16*k≤16*n; omega)
  refine ⟨lay.reads,?_,?_,?_,lay.counterKey,lay.yKey,lay.counterY,by have := lay.size; omega⟩
  · intro p len ⟨r,hr,hp⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact lay.writes _ _ ⟨coreCounter s,by simp,hp⟩
    · exact lay.writes _ _ ⟨coreY s,by simp,hp⟩
    · apply lay.writes p len
      refine ⟨coreData s n,by simp,?_⟩
      change (p-s.gpr .r6).toNat+len≤16*n
      change (p-s.gpr .r6).toNat+len≤16*k at hp
      omega
    · exact lay.writes _ _ ⟨coreWork s,by simp,hp⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact lay.scratch _ (by simp)
    · exact lay.scratch _ (by simp)
    · exact lay.scratch _ (by simp)
    · exact (lay.scratch _ (by simp)).sub_left hsub
  · intro r hr
    exact (lay.data r hr).sub_right hsub


theorem CoreLayout.congr {a b : State} {n : Nat} (lay : CoreLayout a n)
    (h3 : b.gpr .r3=a.gpr .r3) (h5 : b.gpr .r5=a.gpr .r5)
    (h6 : b.gpr .r6=a.gpr .r6) (h9 : b.gpr .r9=a.gpr .r9) (h10 : b.gpr .r10=a.gpr .r10)
    (hrd : b.rd=a.rd) (hwr : b.wr=a.wr) : CoreLayout b n := by
  have hk : coreKey b=coreKey a := congrArg (fun p => (⟨p,256⟩ : Region)) h3
  have hc : coreCounter b=coreCounter a := congrArg (fun p => (⟨p,16⟩ : Region)) h5
  have hd : coreData b n=coreData a n := congrArg (fun p => (⟨p,16*n⟩ : Region)) h6
  have hy : coreY b=coreY a := congrArg (fun p => (⟨p,16⟩ : Region)) h9
  have hw : coreWork b=coreWork a := congrArg (fun p => (⟨p,2048⟩ : Region)) h10
  refine ⟨?_,?_,?_,?_,?_,?_,?_,lay.size⟩
  · simpa only [hk,hrd,hwr] using lay.reads
  · simpa only [hc,hy,hd,hw,hwr] using lay.writes
  · simpa only [hk,hc,hy,hd,hw] using lay.scratch
  · simpa only [hk,hc,hy,hd] using lay.data
  · simpa only [hk,hc] using lay.counterKey
  · simpa only [hk,hy] using lay.yKey
  · simpa only [hc,hy] using lay.counterY


def wrapperView (s : State) : State :=
  ((((s.write .r6 (s.gpr .r7)).write .r7 (s.gpr .r8)).write .r8 (s.gpr .r3+240)).write
    .r9 (s.gpr .r6)).write .r10 (s.gpr .r9+64)

structure WrapperLayout (s : State) (n : Nat) : Prop where
  core : CoreLayout (wrapperView s) n
  header : Covers [⟨s.gpr .r9,64⟩] s.wr
  scratch : ∀ r ∈ [coreKey (wrapperView s),coreCounter (wrapperView s),coreY (wrapperView s),coreData (wrapperView s) n],
    r.Disjoint ⟨s.gpr .r9,2112⟩
  fit : (s.gpr .r7).toNat+16*n≤2^64


theorem wrapperEntry_data (s : State) : (wrapperEntryState s).gpr .r30=s.gpr .r7 := by
  simp only [wrapperEntryState,wrapperConfigState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false]


theorem wrapperEntry_count (s : State) : (wrapperEntryState s).gpr .r25=s.gpr .r8 := by
  simp only [wrapperEntryState,wrapperConfigState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false]


theorem bulkEntry_layout {s : State} {n : Nat} (lay : WrapperLayout s n) :
    CoreLayout (bulkArgsState (wrapperEntryState s)) (n-n%8) := by
  apply (lay.core.prefix (show n-n%8≤n by omega)).congr
  all_goals
    simp only [bulkArgsState,wrapperEntryState,wrapperConfigState,wrapperView,
      RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false,RegUpd.rd_write,RegUpd.wr_write]


theorem ctxCipher_frame {m m' : Mem} {rs : List Region} {p : Addr} {nr : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨p,256⟩ : Region).Disjoint r) (hnr : nr<15) :
    Spec.Gcm.ctxCiph m' p nr=Spec.Gcm.ctxCiph m p nr := by
  unfold Spec.Gcm.ctxCiph
  apply congrArg (Spec.Gcm.aesWith nr)
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p,256⟩) hd (by change 256≤2^64; decide) (by
    have := List.mem_range.mp hi
    change i<256
    omega)


theorem WrapperLayout.header_disjoint {s : State} {n : Nat} (lay : WrapperLayout s n)
    {r : Region} (hr : r ∈ [coreKey (wrapperView s),coreCounter (wrapperView s),coreY (wrapperView s),
      coreData (wrapperView s) n]) : r.Disjoint ⟨s.gpr .r9,64⟩ :=
  (lay.scratch r hr).sub_right (Region.sub_prefix (by decide))


theorem header_ctxCipher {s : State} {n nr : Nat} (lay : WrapperLayout s n) (hnr : nr<15) :
    Spec.Gcm.ctxCiph (wrapperHeaderMem s) (s.gpr .r3) nr=Spec.Gcm.ctxCiph s.mem (s.gpr .r3) nr := by
  apply ctxCipher_frame (wrapperHeader_frame s) _ hnr
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact lay.header_disjoint (r := coreKey (wrapperView s)) (by simp)


theorem header_counter {s : State} {n : Nat} (lay : WrapperLayout s n) :
    Spec.Gcm.blockAt (wrapperHeaderMem s) (s.gpr .r5)=Spec.Gcm.blockAt s.mem (s.gpr .r5) := by
  apply block_frame (wrapperHeader_frame s)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact lay.header_disjoint (r := coreCounter (wrapperView s)) (by simp)


theorem header_y {s : State} {n : Nat} (lay : WrapperLayout s n) :
    Spec.Gcm.blockAt (wrapperHeaderMem s) (s.gpr .r6)=Spec.Gcm.blockAt s.mem (s.gpr .r6) := by
  apply block_frame (wrapperHeader_frame s)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact lay.header_disjoint (r := coreY (wrapperView s)) (by simp)


theorem header_h {s : State} {n : Nat} (lay : WrapperLayout s n) :
    Spec.Gcm.ctxH (wrapperHeaderMem s) (s.gpr .r3)=Spec.Gcm.ctxH s.mem (s.gpr .r3) := by
  apply block_frame (wrapperHeader_frame s)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact (lay.header_disjoint (r := coreKey (wrapperView s)) (by simp)).sub_left
    (Offset.sub_base _ (d := 240) (n := 16) (k := 256) (by decide))


theorem header_data {s : State} {n : Nat} (lay : WrapperLayout s n) :
    Spec.Gcm.blocksAt (wrapperHeaderMem s) (s.gpr .r7) n=Spec.Gcm.blocksAt s.mem (s.gpr .r7) n := by
  apply blocks_frame (wrapperHeader_frame s)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact lay.header_disjoint (r := coreData (wrapperView s) n) (by simp)


theorem bulkRest_pointer (s : State) (n : Nat) (hn : s.gpr .r25=BitVec.ofNat 64 n) :
    (bulkRestState s).gpr .r30=s.gpr .r30+BitVec.ofNat 64 (16*(n-n%8)) ∧
    (bulkRestState s).gpr .r25=BitVec.ofNat 64 (n%8) := by
  have ho : BitVec.ofNat 64 (n-n%8) <<< 4=BitVec.ofNat 64 (16*(n-n%8)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 (n-n%8)*BitVec.ofNat 64 16=_
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  constructor <;> simp only [bulkRestState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false,
    hn,mask_tail,Offset.ofNat_sub_ofNat (Nat.mod_le _ _),ho]


theorem split_ciphertext (m : Mem) (D : Addr) (n k : Nat) (hk : k≤n)
    (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (cb : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph cb (Spec.Gcm.blocksAt m D n)=
      Spec.Gcm.ctr32 ciph cb (Spec.Gcm.blocksAt m D k) ++
      Spec.Gcm.ctr32 ciph (Nat.repeat Spec.Gcm.inc32 k cb)
        (Spec.Gcm.blocksAt m (D+BitVec.ofNat 64 (16*k)) (n-k)) := by
  have he : n=k+(n-k) := by omega
  have hb := VG.Proof.Gcm.blocksAt_add m D k (n-k)
  rw [← he] at hb
  rw [hb,VG.Proof.Gcm.ctr32_append]
  simp only [Spec.Gcm.blocksAt,List.length_map,List.length_range]


def wrapperWrites (s : State) (n : Nat) : List Region :=
  [coreWork (wrapperView s),coreData (wrapperView s) n,coreCounter (wrapperView s),coreY (wrapperView s)]

def wrapperCiphertext (s : State) (nr n : Nat) : List Spec.Gcm.Block :=
  Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph s.mem (s.gpr .r3) nr) (Spec.Gcm.blockAt s.mem (s.gpr .r5))
    (Spec.Gcm.blocksAt s.mem (s.gpr .r7) n)

structure WrapperMid (base : State) (n nr k : Nat) (s : State) : Prop where
  bound : k≤n
  fixed : WrapperFixed base s
  ptr : s.gpr .r30=base.gpr .r7+BitVec.ofNat 64 (16*k)
  count : s.gpr .r25=BitVec.ofNat 64 (n-k)
  keep : ∀ r ∈ preserved, r ∉ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst → s.gpr r=base.gpr r
  frame : Frame (wrapperWrites base n) (wrapperHeaderMem base) s.mem
  completed : Spec.Gcm.blocksAt s.mem (base.gpr .r7) k=wrapperCiphertext base nr k
  pending : Spec.Gcm.blocksAt s.mem (base.gpr .r7+BitVec.ofNat 64 (16*k)) (n-k)=
    Spec.Gcm.blocksAt base.mem (base.gpr .r7+BitVec.ofNat 64 (16*k)) (n-k)
  counter : Spec.Gcm.blockAt s.mem (base.gpr .r5)=
    Nat.repeat Spec.Gcm.inc32 k (Spec.Gcm.blockAt base.mem (base.gpr .r5))
  y : Spec.Gcm.blockAt s.mem (base.gpr .r6)=Spec.Gcm.ghashFrom
    (Spec.Gcm.ctxH base.mem (base.gpr .r3)) (Spec.Gcm.blockAt base.mem (base.gpr .r6)) (wrapperCiphertext base nr k)


theorem wrapperEntry_keep (s : State) {n : Nat} (lay : WrapperLayout s n) :
    Keep (coreVolatile++Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst) s (wrapperEntryState s) := by
  have hw : ∀ off, off+8≤64 → InRegions s.wr (s.gpr .r9+BitVec.ofNat 64 off) 8 := by
    intro off ho
    exact lay.header _ _ ⟨⟨s.gpr .r9,64⟩,by simp,Offset.contains_base _ ho (by omega)⟩
  obtain ⟨_,_,_,he,hk⟩ := WP.keep (coreVolatile++Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst)
    (wrapperEntry_ok s hw) (by lit_decide) (by lit_decide)
  subst he
  exact hk



theorem wrapperEntry_mem (s : State) : (wrapperEntryState s).mem=wrapperHeaderMem s := rfl


theorem wrapperMid_initial (s : State) (n nr : Nat) (lay : WrapperLayout s n)
    (hn : s.gpr .r8=BitVec.ofNat 64 n) : WrapperMid s n nr 0 (wrapperEntryState s) := by
  refine ⟨by omega,wrapperEntry_fixed s,?_,?_,?_,Frame.refl _ _,?_,?_,?_,?_⟩
  · simpa only [Nat.mul_zero,BitVec.add_zero] using wrapperEntry_data s
  · simpa only [Nat.sub_zero] using (wrapperEntry_count s).trans hn
  · intro r hr hn
    apply (wrapperEntry_keep s lay).gpr
    have hpres : ∀ r ∈ preserved, r ∉ coreVolatile := by decide
    simpa only [List.mem_append,not_or] using And.intro (hpres r hr) hn
  · simp only [wrapperCiphertext,Spec.Gcm.blocksAt,List.range_zero,List.map_nil,Spec.Gcm.ctr32,
      Spec.Gcm.keystream,List.length_nil,List.zipWith_nil_left]
  · simpa only [Nat.mul_zero,BitVec.add_zero,Nat.sub_zero,wrapperEntry_mem] using header_data lay
  · exact header_counter lay
  · simpa only [wrapperCiphertext,Spec.Gcm.blocksAt,List.range_zero,List.map_nil,Spec.Gcm.ctr32,
      Spec.Gcm.keystream,List.length_nil,List.zipWith_nil_left,Spec.Gcm.ghashFrom,List.foldl_nil,wrapperEntry_mem] using header_y lay


theorem header_data_prefix {s : State} {n k : Nat} (lay : WrapperLayout s n) (hk : k≤n) :
    Spec.Gcm.blocksAt (wrapperHeaderMem s) (s.gpr .r7) k=Spec.Gcm.blocksAt s.mem (s.gpr .r7) k := by
  apply blocks_frame (wrapperHeader_frame s)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact (lay.header_disjoint (r := coreData (wrapperView s) n) (by simp)).sub_left
    (Region.sub_prefix (by change 16*k≤16*n; omega))


theorem header_data_suffix {s : State} {n k : Nat} (lay : WrapperLayout s n) (hk : k≤n) :
    Spec.Gcm.blocksAt (wrapperHeaderMem s) (s.gpr .r7+BitVec.ofNat 64 (16*k)) (n-k)=
      Spec.Gcm.blocksAt s.mem (s.gpr .r7+BitVec.ofNat 64 (16*k)) (n-k) := by
  apply blocks_frame (wrapperHeader_frame s)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact (lay.header_disjoint (r := coreData (wrapperView s) n) (by simp)).sub_left
    (Offset.sub_base _ (d := 16*k) (n := 16*(n-k)) (k := 16*n) (by omega))


theorem bulk_output {s u : State} {n nr : Nat} (lay : WrapperLayout s n) (hnr : nr<15)
    (hc : CoreResult (bulkArgsState (wrapperEntryState s)) (n-n%8) nr u) :
    Spec.Gcm.blocksAt u.mem (s.gpr .r7) (n-n%8)=wrapperCiphertext s nr (n-n%8) ∧
    Spec.Gcm.blockAt u.mem (s.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (n-n%8) (Spec.Gcm.blockAt s.mem (s.gpr .r5)) ∧
    Spec.Gcm.blockAt u.mem (s.gpr .r6)=Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem (s.gpr .r3))
      (Spec.Gcm.blockAt s.mem (s.gpr .r6)) (wrapperCiphertext s nr (n-n%8)) := by
  have hd : Spec.Gcm.blocksAt u.mem (s.gpr .r7) (n-n%8)=Spec.Gcm.ctr32
      (Spec.Gcm.ctxCiph (wrapperHeaderMem s) (s.gpr .r3) nr)
      (Spec.Gcm.blockAt (wrapperHeaderMem s) (s.gpr .r5))
      (Spec.Gcm.blocksAt (wrapperHeaderMem s) (s.gpr .r7) (n-n%8)) := hc.ciphertext
  rw [header_ctxCipher lay hnr,header_counter lay,header_data_prefix lay (by omega)] at hd
  have hctr : Spec.Gcm.blockAt u.mem (s.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (n-n%8)
      (Spec.Gcm.blockAt (wrapperHeaderMem s) (s.gpr .r5)) := hc.counter
  rw [header_counter lay] at hctr
  have hy : Spec.Gcm.blockAt u.mem (s.gpr .r6)=Spec.Gcm.ghashFrom
      (Spec.Gcm.ctxH (wrapperHeaderMem s) (s.gpr .r3)) (Spec.Gcm.blockAt (wrapperHeaderMem s) (s.gpr .r6))
      (Spec.Gcm.blocksAt u.mem (s.gpr .r7) (n-n%8)) := hc.y
  rw [header_h lay,header_y lay,hd] at hy
  exact ⟨hd,hctr,hy⟩


theorem bulk_pending {s u : State} {n nr : Nat} (lay : WrapperLayout s n)
    (hc : CoreResult (bulkArgsState (wrapperEntryState s)) (n-n%8) nr u) :
    Spec.Gcm.blocksAt u.mem (s.gpr .r7+BitVec.ofNat 64 (16*(n-n%8))) (n-(n-n%8))=
      Spec.Gcm.blocksAt s.mem (s.gpr .r7+BitVec.ofNat 64 (16*(n-n%8))) (n-(n-n%8)) := by
  have hf : Frame [coreWork (wrapperView s),coreData (wrapperView s) (n-n%8),
      coreCounter (wrapperView s),coreY (wrapperView s)] (wrapperHeaderMem s) u.mem := hc.frame
  refine (blocks_frame hf ?_).trans (header_data_suffix lay (by omega))
  intro r hr
  have hsub : Region.Sub (⟨s.gpr .r7+BitVec.ofNat 64 (16*(n-n%8)),16*(n-(n-n%8))⟩ : Region)
      (coreData (wrapperView s) n) := Offset.sub_base _ (by omega)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (lay.core.scratch (coreData (wrapperView s) n) (by simp)).sub_left hsub
  · exact Offset.disjoint_base _ (by omega) (by have := lay.core.size; omega)
  · exact (lay.core.data (coreCounter (wrapperView s)) (by simp)).symm.sub_left hsub
  · exact (lay.core.data (coreY (wrapperView s)) (by simp)).symm.sub_left hsub


theorem bulkRest_keep (s : State) : Keep (coreVolatile++([.r25,.r30] : List Reg)) s (bulkRestState s) := by
  obtain ⟨_,_,_,he,hk⟩ := WP.keep (coreVolatile++([.r25,.r30] : List Reg)) (bulkRest_ok s) (by lit_decide) (by lit_decide)
  subst he
  exact hk


theorem bulkRest_fixed {base s : State} (hf : WrapperFixed base s) : WrapperFixed base (bulkRestState s) := by
  refine ⟨hf.rd,hf.wr,?_,?_,?_,?_,?_⟩
  all_goals simp only [bulkRestState,RegUpd.gpr_write,reduceCtorEq,ite_false]
  · exact hf.ctx
  · exact hf.rounds
  · exact hf.counter
  · exact hf.y
  · exact hf.work


theorem bulkRest_mem (s : State) : (bulkRestState s).mem=s.mem := rfl


theorem bulk_frame {s u : State} {n nr : Nat}
    (hc : CoreResult (bulkArgsState (wrapperEntryState s)) (n-n%8) nr u) :
    Frame (wrapperWrites s n) (wrapperHeaderMem s) u.mem := by
  have hf : Frame [coreWork (wrapperView s),coreData (wrapperView s) (n-n%8),
      coreCounter (wrapperView s),coreY (wrapperView s)] (wrapperHeaderMem s) u.mem := hc.frame
  apply hf.sub
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨coreWork (wrapperView s),by simp [wrapperWrites],fun _ h => h⟩
  · exact ⟨coreData (wrapperView s) n,by simp [wrapperWrites],
      Region.sub_prefix (by change 16*(n-n%8)≤16*n; omega)⟩
  · exact ⟨coreCounter (wrapperView s),by simp [wrapperWrites],fun _ h => h⟩
  · exact ⟨coreY (wrapperView s),by simp [wrapperWrites],fun _ h => h⟩


theorem wrapper_bulk_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (n nr : Nat) (lay : WrapperLayout s n) (hn : s.gpr .r8=BitVec.ofNat 64 n)
    (hr : s.gpr .r4=BitVec.ofNat 64 nr) (hmin : 9<nr) (hmax : nr<15) :
    WP isa (.seq (.block Impl.AesGcm.PPC64LE.Blocks.bulkArgs)
      (.seq Impl.AesGcm.PPC64LE.Blocks.code (.block Impl.AesGcm.PPC64LE.Blocks.bulkRest)))
      (wrapperEntryState s) (WrapperMid s n nr (n-n%8)) := by
  apply WP.seq
  refine WP.mono (bulkArgs_ok (wrapperEntryState s)) fun args hargs => ?_
  subst args
  have ha := bulkArgs_result (wrapperEntry_fixed s) ((wrapperEntry_count s).trans hn)
  have hH : (bulkArgsState (wrapperEntryState s)).gpr .r8=
      (bulkArgsState (wrapperEntryState s)).gpr .r3+240#64 := by
    rw [ha.h,ha.ctx]
    rfl
  have hnr : (bulkArgsState (wrapperEntryState s)).gpr .r4=BitVec.ofNat 64 nr := ha.rounds.trans hr
  apply WP.seq
  refine WP.mono (core_ok _ (n-n%8) nr (bulkEntry_layout lay) ha.left (by omega) hmin hmax hnr hH)
    fun u ⟨hu,hku⟩ => ?_
  refine WP.mono (bulkRest_ok u) fun t ht => ?_
  subst t
  have h25 : u.gpr .r25=BitVec.ofNat 64 n :=
    (hku.gpr (by decide)).trans (((bulkArgs_keep _).gpr (by decide)).trans ((wrapperEntry_count s).trans hn))
  have h30 : u.gpr .r30=s.gpr .r7 :=
    (hku.gpr (by decide)).trans (((bulkArgs_keep _).gpr (by decide)).trans (wrapperEntry_data s))
  have hp := bulkRest_pointer u n h25
  have hout := bulk_output lay hmax hu
  have hkeep := ((((wrapperEntry_keep s lay).trans (bulkArgs_keep _)).trans hku).trans (bulkRest_keep u))
  refine ⟨by omega,bulkRest_fixed (ha.fixed.keep hku),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hp.1.trans (congrArg (fun p => p+BitVec.ofNat 64 (16*(n-n%8))) h30)
  · simpa only [show n-(n-n%8)=n%8 by omega] using hp.2
  · intro r hr hs
    have hpres : ∀ r ∈ preserved, r ∉ coreVolatile := by decide
    have hv := hpres r hr
    have h25 : r≠.r25 := fun he => hs (by simp [Impl.AesGcm.PPC64LE.Blocks.wrapperSaved,he])
    have h30 : r≠.r30 := fun he => hs (by simp [Impl.AesGcm.PPC64LE.Blocks.wrapperSaved,he])
    exact hkeep.gpr (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨⟨⟨⟨hv,hs⟩,hv⟩,hv⟩,hv,h25,h30⟩)
  · simpa only [bulkRest_mem] using bulk_frame hu
  · simpa only [bulkRest_mem] using hout.1
  · simpa only [bulkRest_mem] using bulk_pending lay hu
  · simpa only [bulkRest_mem] using hout.2.1
  · simpa only [bulkRest_mem] using hout.2.2


theorem wrapper_bulk_test (s : State) {n : Nat} (hn : s.gpr .r8=BitVec.ofNat 64 n) (hlt : n<2^64) :
    (wrapperEntryState s).gpr .r12=0 ↔ n<32 := by
  have he : (wrapperEntryState s).gpr .r12=BitVec.ofNat 64 n >>> 5 := by
    simp only [wrapperEntryState,wrapperConfigState,RegUpd.gpr_write_self,RegUpd.gpr_write,
      reduceCtorEq,ite_false,hn]
  rw [he]
  constructor
  · intro hz
    have hh := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hlt,Nat.shiftRight_eq_div_pow] at hh
    change n/32=0 at hh
    omega
  · intro hz
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hlt,Nat.shiftRight_eq_div_pow]
    change n/32=0
    exact Nat.div_eq_of_lt hz


theorem wrapper_optional_bulk_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (n nr : Nat) (lay : WrapperLayout s n) (hn : s.gpr .r8=BitVec.ofNat 64 n)
    (hr : s.gpr .r4=BitVec.ofNat 64 nr) (hmin : 9<nr) (hmax : nr<15) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.maybeBulk (wrapperEntryState s)
      fun t => ∃ k, k≤n ∧ n-k<32 ∧ WrapperMid s n nr k t := by
  rw [Impl.AesGcm.PPC64LE.Blocks.maybeBulk]
  have ht := wrapper_bulk_test s hn (by have := lay.core.size; omega)
  by_cases hsmall : n<32
  · refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,ht.mpr hsmall]; rfl)
      (fun _ => WP.block_nil ⟨0,by omega,by omega,wrapperMid_initial s n nr lay hn⟩) (by simp)
  · have hne : (wrapperEntryState s).gpr .r12≠0 := fun he => hsmall (ht.mp he)
    refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
      Option.some.injEq,beq_eq_false_iff_ne] using hne) (by simp) (fun _ => ?_)
    exact WP.mono (wrapper_bulk_ok s n nr lay hn hr hmin hmax) fun t hh =>
      ⟨n-n%8,by omega,by omega,hh⟩


theorem CoreLayout.slice {s : State} {n k j : Nat} (lay : CoreLayout s n) (hk : k+j≤n) :
    CoreLayout (s.write .r6 (s.gpr .r6+BitVec.ofNat 64 (16*k))) j := by
  have hsub : Region.Sub (⟨s.gpr .r6+BitVec.ofNat 64 (16*k),16*j⟩ : Region) (coreData s n) :=
    Offset.sub_base _ (by omega)
  refine ⟨lay.reads,?_,?_,?_,lay.counterKey,lay.yKey,lay.counterY,by have := lay.size; omega⟩
  · apply Covers.trans ?_ lay.writes
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨coreCounter s,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤16; decide⟩
    · exact ⟨coreY s,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤16; decide⟩
    · exact ⟨coreData s n,by simp,16*k,rfl,by change 16*k+16*j≤16*n; omega⟩
    · exact ⟨coreWork s,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+2048≤2048; decide⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact lay.scratch (coreKey s) (by simp)
    · exact lay.scratch (coreCounter s) (by simp)
    · exact lay.scratch (coreY s) (by simp)
    · exact (lay.scratch (coreData s n) (by simp)).sub_left hsub
  · intro r hr
    exact (lay.data r hr).sub_right hsub


theorem wrapper_tail_config {base s : State} {n nr k : Nat} (lay : WrapperLayout base n)
    (hs : WrapperMid base n nr k s) (hnr : base.gpr .r4=BitVec.ofNat 64 nr)
    (hv : nr=10 ∨ nr=12 ∨ nr=14) : TailConfig s (n-k) nr := by
  have hl : CoreLayout (tailBase s) (n-k) := by
    apply (lay.core.slice (k := k) (j := n-k) (by have := hs.bound; omega)).congr
    · change (tailBase s).gpr .r3=(wrapperView base).gpr .r3
      simpa only [tailBase,bulkArgsState,wrapperView,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false] using hs.fixed.ctx
    · change (tailBase s).gpr .r5=(wrapperView base).gpr .r5
      simpa only [tailBase,bulkArgsState,wrapperView,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false] using hs.fixed.counter
    · simpa only [tailBase,bulkArgsState,wrapperView,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false] using hs.ptr
    · simpa only [tailBase,bulkArgsState,wrapperView,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false] using hs.fixed.y
    · simpa only [tailBase,bulkArgsState,wrapperView,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false] using
        congrArg (fun p => p+64) hs.fixed.work
    · exact hs.fixed.rd
    · exact hs.fixed.wr
  refine ⟨hl,hs.count,hs.fixed.rounds.trans hnr,hv,?_⟩
  rw [hs.ptr,BitVec.toNat_add,BitVec.toNat_ofNat]
  have hle : ((base.gpr .r7).toNat+(16*k)%2^64)%2^64≤(base.gpr .r7).toNat+16*k :=
    Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  have := lay.fit
  have := hs.bound
  omega


theorem WrapperLayout.key_apart {base : State} {n : Nat} (lay : WrapperLayout base n) :
    ∀ r ∈ wrapperWrites base n, (coreKey (wrapperView base)).Disjoint r := by
  intro r hr
  simp only [wrapperWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact lay.core.scratch _ (by simp)
  · exact lay.core.data _ (by simp)
  · exact lay.core.counterKey
  · exact lay.core.yKey


theorem wrapper_ctxCipher {base : State} {m : Mem} {n nr : Nat} (lay : WrapperLayout base n)
    (hf : Frame (wrapperWrites base n) (wrapperHeaderMem base) m) (hnr : nr<15) :
    Spec.Gcm.ctxCiph m (base.gpr .r3) nr=Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr :=
  (ctxCipher_frame hf lay.key_apart hnr).trans (header_ctxCipher lay hnr)


theorem wrapper_h {base : State} {m : Mem} {n : Nat} (lay : WrapperLayout base n)
    (hf : Frame (wrapperWrites base n) (wrapperHeaderMem base) m) :
    Spec.Gcm.ctxH m (base.gpr .r3)=Spec.Gcm.ctxH base.mem (base.gpr .r3) := by
  refine (block_frame hf ?_).trans (header_h lay)
  intro r hr
  exact (lay.key_apart r hr).sub_left (Offset.sub_base _ (d := 240) (n := 16) (k := 256) (by decide))


theorem WrapperLayout.header_apart {base : State} {n : Nat} (lay : WrapperLayout base n) :
    ∀ r ∈ wrapperWrites base n, (⟨base.gpr .r9,64⟩ : Region).Disjoint r := by
  intro r hr
  simp only [wrapperWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.base_disjoint _ (e := 64) (n := 2048) (k := 64) (by decide) (by decide)
  · exact (lay.scratch (coreData (wrapperView base) n) (by simp)).symm.sub_left (Region.sub_prefix (by decide))
  · exact (lay.scratch (coreCounter (wrapperView base)) (by simp)).symm.sub_left (Region.sub_prefix (by decide))
  · exact (lay.scratch (coreY (wrapperView base)) (by simp)).symm.sub_left (Region.sub_prefix (by decide))


theorem wrapper_saved {base : State} {m : Mem} {n : Nat} (lay : WrapperLayout base n)
    (hf : Frame (wrapperWrites base n) (wrapperHeaderMem base) m) :
    Spill.Saved (base.gpr .r9) base.gpr Impl.AesGcm.PPC64LE.Blocks.wrapperSaved m ∧
      m.readW (base.gpr .r9+56) 64=base.lr := by
  constructor
  · refine (wrapperHeader_saved base).frame hf fun p hp r hr => ?_
    have ho : ∀ p ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved, p.2+8≤64 := by decide
    exact (lay.header_apart r hr).sub_left (Offset.sub_base _ (d := p.2) (n := 8) (k := 64) (ho p hp))
  · rw [hf.readW (r := ⟨base.gpr .r9,64⟩)
      (Offset.contains_base _ (d := 56) (n := 8) (k := 64) (by decide) (by decide)) lay.header_apart (by decide)]
    exact wrapperHeader_lr base


structure WrapperDone (base : State) (n nr : Nat) (s : State) : Prop where
  fixed : WrapperFixed base s
  keep : ∀ r ∈ preserved, r ∉ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst → s.gpr r=base.gpr r
  frame : Frame (wrapperWrites base n) (wrapperHeaderMem base) s.mem
  ciphertext : Spec.Gcm.blocksAt s.mem (base.gpr .r7) n=wrapperCiphertext base nr n
  counter : Spec.Gcm.blockAt s.mem (base.gpr .r5)=
    Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt base.mem (base.gpr .r5))
  y : Spec.Gcm.blockAt s.mem (base.gpr .r6)=Spec.Gcm.ghashFrom
    (Spec.Gcm.ctxH base.mem (base.gpr .r3)) (Spec.Gcm.blockAt base.mem (base.gpr .r6))
    (Spec.Gcm.blocksAt s.mem (base.gpr .r7) n)


theorem wrapper_tail_ok [VG.Proof.Gcm.PPC64LE.GhashLaw]
    {base s : State} {n nr k : Nat} (lay : WrapperLayout base n) (hs : WrapperMid base n nr k s)
    (hnr : base.gpr .r4=BitVec.ofNat 64 nr) (hv : nr=10 ∨ nr=12 ∨ nr=14) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.tail s (WrapperDone base n nr) := by
  refine WP.mono (tail_ok s (n-k) nr (wrapper_tail_config lay hs hnr hv)) fun t ht => ?_
  have hft : Frame [coreCounter (wrapperView base),coreY (wrapperView base),
      ⟨base.gpr .r7+BitVec.ofNat 64 (16*k),16*(n-k)⟩,coreWork (wrapperView base)] s.mem t.mem := by
    have hh := ht.frame
    change Frame [⟨s.gpr .r27,16⟩,⟨s.gpr .r26,16⟩,⟨s.gpr .r30,16*(n-k)⟩,⟨s.gpr .r31+64,2048⟩] s.mem t.mem at hh
    rw [hs.fixed.counter,hs.fixed.y,hs.ptr,hs.fixed.work] at hh
    exact hh
  have hprefix : Spec.Gcm.blocksAt t.mem (base.gpr .r7) k=wrapperCiphertext base nr k := by
    refine (blocks_frame hft ?_).trans hs.completed
    intro r hr
    have hsub : Region.Sub (⟨base.gpr .r7,16*k⟩ : Region) (coreData (wrapperView base) n) :=
      Region.sub_prefix (by change 16*k≤16*n; have := hs.bound; omega)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (lay.core.data (coreCounter (wrapperView base)) (by simp)).symm.sub_left hsub
    · exact (lay.core.data (coreY (wrapperView base)) (by simp)).symm.sub_left hsub
    · exact Offset.base_disjoint _ (by omega) (by have := lay.core.size; have := hs.bound; omega)
    · exact (lay.core.scratch (coreData (wrapperView base) n) (by simp)).sub_left hsub
  have hsubout := ht.ciphertext
  rw [hs.fixed.ctx,hs.ptr,hs.fixed.counter,wrapper_ctxCipher lay hs.frame (by rcases hv with h | h | h <;> omega),
    hs.counter,hs.pending] at hsubout
  have hsplit : Spec.Gcm.blocksAt t.mem (base.gpr .r7) n=wrapperCiphertext base nr k ++
      Spec.Gcm.blocksAt t.mem (base.gpr .r7+BitVec.ofNat 64 (16*k)) (n-k) := by
    have hh := VG.Proof.Gcm.blocksAt_add t.mem (base.gpr .r7) k (n-k)
    rw [show k+(n-k)=n by have := hs.bound; omega,hprefix] at hh
    exact hh
  have hout : Spec.Gcm.blocksAt t.mem (base.gpr .r7) n=wrapperCiphertext base nr n := by
    rw [hsplit,hsubout]
    simp only [wrapperCiphertext]
    rw [split_ciphertext _ _ n k hs.bound]
  have hcounter := ht.counter
  rw [hs.fixed.counter,hs.counter,repeat_counter_add,show k+(n-k)=n by have := hs.bound; omega] at hcounter
  have hy := ht.y
  rw [hs.fixed.y,hs.fixed.ctx,hs.ptr,wrapper_h lay hs.frame,hs.y] at hy
  have hf : Frame (wrapperWrites base n) s.mem t.mem := hft.sub (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨coreCounter (wrapperView base),by simp [wrapperWrites],fun _ h => h⟩
    · exact ⟨coreY (wrapperView base),by simp [wrapperWrites],fun _ h => h⟩
    · exact ⟨coreData (wrapperView base) n,by simp [wrapperWrites],
        Offset.sub_base _ (d := 16*k) (n := 16*(n-k)) (k := 16*n) (by have := hs.bound; omega)⟩
    · exact ⟨coreWork (wrapperView base),by simp [wrapperWrites],fun _ h => h⟩)
  refine ⟨?_,?_,hs.frame.trans hf,hout,hcounter,?_⟩
  · refine ⟨ht.rd.trans hs.fixed.rd,ht.wr.trans hs.fixed.wr,?_,?_,?_,?_,?_⟩
    · exact (ht.saved .r29 (by decide)).trans hs.fixed.ctx
    · exact (ht.saved .r28 (by decide)).trans hs.fixed.rounds
    · exact (ht.saved .r27 (by decide)).trans hs.fixed.counter
    · exact (ht.saved .r26 (by decide)).trans hs.fixed.y
    · exact (ht.saved .r31 (by decide)).trans hs.fixed.work
  · intro r hr hn
    exact (ht.saved r hr).trans (hs.keep r hr hn)
  · rw [hsplit]
    simpa only [Spec.Gcm.ghashFrom,List.foldl_append] using hy


def wrapperFullWrites (s : State) (n : Nat) : List Region :=
  [⟨s.gpr .r9,2112⟩,coreData (wrapperView s) n,coreCounter (wrapperView s),coreY (wrapperView s)]


theorem wrapper_final_frame {base : State} {m : Mem} {n : Nat}
    (hf : Frame (wrapperWrites base n) (wrapperHeaderMem base) m) :
    Frame (wrapperFullWrites base n) base.mem m := by
  have hh : Frame (wrapperFullWrites base n) base.mem (wrapperHeaderMem base) :=
    (wrapperHeader_frame base).sub (fun r hr => by
      rw [List.mem_singleton] at hr
      subst r
      exact ⟨⟨base.gpr .r9,2112⟩,by simp [wrapperFullWrites],Region.sub_prefix (by decide)⟩)
  apply hh.trans
  apply hf.sub
  intro r hr
  simp only [wrapperWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨base.gpr .r9,2112⟩,by simp [wrapperFullWrites],
      Offset.sub_base _ (d := 64) (n := 2048) (k := 2112) (by decide)⟩
  · exact ⟨coreData (wrapperView base) n,by simp [wrapperFullWrites],fun _ h => h⟩
  · exact ⟨coreCounter (wrapperView base),by simp [wrapperFullWrites],fun _ h => h⟩
  · exact ⟨coreY (wrapperView base),by simp [wrapperFullWrites],fun _ h => h⟩


structure WrapperResult (base : State) (n nr : Nat) (s : State) : Prop where
  rd : s.rd=base.rd
  wr : s.wr=base.wr
  saved : ∀ r ∈ preserved, s.gpr r=base.gpr r
  lr : s.lr=base.lr
  frame : Frame (wrapperFullWrites base n) base.mem s.mem
  ciphertext : Spec.Gcm.blocksAt s.mem (base.gpr .r7) n=wrapperCiphertext base nr n
  counter : Spec.Gcm.blockAt s.mem (base.gpr .r5)=
    Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt base.mem (base.gpr .r5))
  y : Spec.Gcm.blockAt s.mem (base.gpr .r6)=Spec.Gcm.ghashFrom
    (Spec.Gcm.ctxH base.mem (base.gpr .r3)) (Spec.Gcm.blockAt base.mem (base.gpr .r6)) (wrapperCiphertext base nr n)


theorem wrapper_finish {base s : State} {n nr : Nat} (lay : WrapperLayout base n)
    (hs : WrapperDone base n nr s) :
    WP isa (.block Impl.AesGcm.PPC64LE.Blocks.wrapperExit) s (WrapperResult base n nr) := by
  have hv := wrapper_saved lay hs.frame
  have hr : ∀ off, off+8≤64 → InRegions (s.rd++s.wr) (base.gpr .r9+BitVec.ofNat 64 off) 8 := by
    intro off ho
    rw [hs.fixed.rd,hs.fixed.wr]
    exact Covers.right lay.header _ _ ⟨⟨base.gpr .r9,64⟩,by simp,Offset.contains_base _ ho (by omega)⟩
  refine WP.mono (wrapperExit_ok base s hs.fixed.work hv.1 hv.2 hr) fun t ht => ?_
  refine ⟨ht.rd.trans hs.fixed.rd,ht.wr.trans hs.fixed.wr,?_,ht.lr,?_,?_,?_,?_⟩
  · intro r hr
    by_cases hm : r ∈ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
      exact ht.restored p hp
    · have hnot : ∀ r ∈ preserved, r≠.r0 ∧ r≠.r12 := by decide
      rw [ht.other r (by simpa only [List.mem_cons,not_or] using And.intro (hnot r hr).1 (And.intro (hnot r hr).2 hm))]
      exact hs.keep r hr hm
  · simpa only [ht.mem] using wrapper_final_frame hs.frame
  · simpa only [ht.mem] using hs.ciphertext
  · simpa only [ht.mem] using hs.counter
  · simpa only [ht.mem,hs.ciphertext] using hs.y


theorem wrapper_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (n nr : Nat) (lay : WrapperLayout s n) (hn : s.gpr .r8=BitVec.ofNat 64 n)
    (hr : s.gpr .r4=BitVec.ofNat 64 nr) (hv : nr=10 ∨ nr=12 ∨ nr=14) :
    WP isa Impl.AesGcm.PPC64LE.Blocks.encrypt s (WrapperResult s n nr) := by
  rw [Impl.AesGcm.PPC64LE.Blocks.encrypt]
  by_cases hz : n=0
  · subst n
    refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hn]; rfl)
      (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨rfl,rfl,fun _ _ => rfl,rfl,Frame.refl _ _,?_,rfl,?_⟩
    · simp only [wrapperCiphertext,Spec.Gcm.blocksAt,List.range_zero,List.map_nil,Spec.Gcm.ctr32,
        Spec.Gcm.keystream,List.length_nil,List.zipWith_nil_left]
    · rfl
  · have hne : s.gpr .r8≠0 := by
      intro he
      have hh := congrArg BitVec.toNat he
      rw [hn,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := lay.core.size; omega)] at hh
      exact hz hh
    refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
      Option.some.injEq,beq_eq_false_iff_ne] using hne) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (wrapperEntry_ok s (fun off ho => lay.header _ _
      ⟨⟨s.gpr .r9,64⟩,by simp,Offset.contains_base _ ho (by omega)⟩)) fun entry he => ?_
    subst entry
    apply WP.seq
    refine WP.mono (wrapper_optional_bulk_ok s n nr lay hn hr
      (by rcases hv with h | h | h <;> omega) (by rcases hv with h | h | h <;> omega)) fun mid hm => ?_
    obtain ⟨k,_,_,hm⟩ := hm
    apply WP.seq
    refine WP.mono (wrapper_tail_ok lay hm hr hv) fun done hd => ?_
    exact wrapper_finish lay hd


theorem shared_pre (s : State) (hs : (Spec.Gcm.encryptBlocksContract PPC64LE.abi).pre s) :
    WrapperLayout s (s.gpr .r8).toNat ∧
      ((s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14) := by
  sig_eval [Spec.Gcm.encryptBlocksContract,Spec.Gcm.cryptBlocksSig,PPC64LE.abi,PPC64LE.argRegs] at hs
  obtain ⟨hrd,hwr,hkc,hky,hkd,hks,hcy,hcd,hcs,hyd,hys,hds,hK,hC,hY,hD,hS,hnr⟩ := hs
  rw [Nat.mul_comm (s.gpr .r8).toNat 16] at hwr hkd hcd hyd hds hD
  have hsub : Region.Sub (coreWork (wrapperView s)) (⟨s.gpr .r9,2112⟩ : Region) :=
    Offset.sub_base _ (d := 64) (n := 2048) (k := 2112) (by decide)
  refine ⟨⟨?_,?_,?_,hD⟩,hnr⟩
  · refine ⟨?_,?_,?_,?_,hkc,hky,hcy,by omega⟩
    · change Covers [⟨s.gpr .r3,256⟩] (s.rd++s.wr)
      rw [hrd]
      exact Covers.of_mem (by simp)
    · change Covers [⟨s.gpr .r5,16⟩,⟨s.gpr .r6,16⟩,⟨s.gpr .r7,16*(s.gpr .r8).toNat⟩,
        ⟨s.gpr .r9+64,2048⟩] s.wr
      rw [hwr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨s.gpr .r5,16⟩,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤16; decide⟩
      · exact ⟨⟨s.gpr .r6,16⟩,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤16; decide⟩
      · exact ⟨⟨s.gpr .r7,16*(s.gpr .r8).toNat⟩,by simp,0,by exact (BitVec.add_zero _).symm,by omega⟩
      · exact ⟨⟨s.gpr .r9,2112⟩,by simp,64,rfl,by change 64+2048≤2112; decide⟩
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hks.sub_right hsub
      · exact hcs.sub_right hsub
      · exact hys.sub_right hsub
      · exact hds.sub_right hsub
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hkd,hcd,hyd]
  · rw [hwr]
    apply Covers.of_sub
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨⟨s.gpr .r9,2112⟩,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+64≤2112; decide⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hks,hcs,hys,hds]


theorem code_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10])
    Impl.AesGcm.PPC64LE.Blocks.code h).isSome = true := ⟨_, by taint_decide⟩

theorem encrypt_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    Impl.AesGcm.PPC64LE.Blocks.encrypt h).isSome = true := ⟨_, by taint_decide⟩

theorem encrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (hs : (Spec.Gcm.encryptBlocksContract PPC64LE.abi).pre s) :
    ∃ tr t, Exec isa Impl.AesGcm.PPC64LE.Blocks.encrypt s tr t ∧ abiPreserved s t ∧
      (Spec.Gcm.encryptBlocksContract PPC64LE.abi).post s t := by
  have hp := shared_pre s hs
  obtain ⟨tr,t,he,ht⟩ := wrapper_ok s (s.gpr .r8).toNat (s.gpr .r4).toNat hp.1
    (by simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq])
    (by simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]) hp.2
  refine ⟨tr,t,he,⟨ht.saved,Exec.sp he,ht.lr⟩,?_⟩
  sig_eval [Spec.Gcm.encryptBlocksContract,Spec.Gcm.cryptBlocksSig,PPC64LE.abi,PPC64LE.argRegs]
  exact ⟨ht.ciphertext,ht.counter,ht.y⟩


theorem encrypt_ct : ConstantTime isa (Spec.Gcm.encryptBlocksContract PPC64LE.abi).pre
    (Spec.Gcm.encryptBlocksContract PPC64LE.abi).pub Impl.AesGcm.PPC64LE.Blocks.encrypt := by
  refine VG.Taint.constantTime_of_exists (A := vectorTaint) (Taint.ofRegs [.r3,.r4,.r5,.r6,.r7,.r8,.r9])
    ?_ encrypt_taint
  intro s t _ _ hp
  sig_pub [Spec.Gcm.encryptBlocksContract,Spec.Gcm.cryptBlocksSig,PPC64LE.abi,PPC64LE.argRegs] at hp
  obtain ⟨hsp,h3,h4,h5,h6,h7,h8,h9⟩ := hp
  refine ⟨hsp,fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption


def encryptSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r7 => 0x4000 | .r9 => 0x5000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000,256⟩]
  wr := [⟨0x2000,16⟩,⟨0x3000,16⟩,⟨0x4000,0⟩,⟨0x5000,2112⟩]


theorem encrypt_sat : (Spec.Gcm.encryptBlocksContract PPC64LE.abi).pre encryptSat := by
  sig_eval [Spec.Gcm.encryptBlocksContract,Spec.Gcm.cryptBlocksSig,PPC64LE.abi,PPC64LE.argRegs,encryptSat]
  refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,by decide,by decide,by decide,by decide,by decide,by decide⟩
  all_goals exact Offset.disjoint_of_le (by decide) (by decide)


theorem encrypt_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target Impl.AesGcm.PPC64LE.Blocks.encrypt (Spec.Gcm.encryptBlocksContract PPC64LE.abi) :=
  ⟨encrypt_correct,encrypt_ct,⟨encryptSat,encrypt_sat⟩⟩


end VG.Proof.AesGcm.PPC64LE.Blocks
