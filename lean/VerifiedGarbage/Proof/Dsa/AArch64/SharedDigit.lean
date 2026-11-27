module

public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Dsa.AArch64.SharedBucket`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SharedStore`, which this module and modules that import it used -/

section

/-! # The masked store of the shared exponentiation's secret bucket

`SharedPower.store` rewrites the first eight table entries, 64 bytes of
each at a time: the entry whose index is the digit takes `[aT]`, and every
other entry is written back as it was. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowVector
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)
open VG.Impl.Dsa.AArch64.SharedPower

theorem write_read_self (m : Mem) (a : Addr) (n : Nat) : m.write a n (m.read a n) = m := by
  funext x
  by_cases h : (x - a).toNat < n
  · simp only [Mem.write, h, ite_true]
    rw [Mem.extractLsb'_read m a h]
    congr 1
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · exact Mem.write_apply h

/-- Everything but memory and `v21` is unchanged. -/
structure MKeep (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ q, q ≠ .v21 → t.v q = s.v q

theorem MKeep.refl (s : State) : MKeep s s := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem MKeep.trans {s t u : State} (h : MKeep s t) (k : MKeep t u) : MKeep s u :=
  ⟨k.gpr.trans h.gpr, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    fun q hq => (k.v q hq).trans (h.v q hq)⟩

/-- A load, BIT and store at one address: the accumulator's 16 bytes are
written under the mask, and the bytes read are written back otherwise. -/
theorem chunk_ok {s : State} {r : VReg} {i : Nat} {choose : Prop} [Decidable choose]
    (hr : r ≠ .v21) (hi : i < 4)
    (hm : s.v .v20 = if choose then BitVec.allOnes 128 else 0)
    (hld : InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16)
    (hst : InRegions s.wr (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block [.ldrq .v21 .x16 (16 * i), .vop (.bsel .bit .v21 r .v20), .strq .v21 .x16 (16 * i)]) s
      fun t => t.mem = (if choose then s.mem.write (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 (s.v r)
        else s.mem) ∧ MKeep s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, addr, show 16 * i % 16 = 0 by omega_using [],
    show 16 * i < 4096 * 16 by omega_using [hi], and_self, ite_true, Option.bind_some,
    State.load, hld, Option.map_some, runStep_some, reduceVOpEval,
    RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ (show VReg.v20 ≠ .v21 by decide),
    RegUpd.v_setV_of_ne _ _ hr, hm, bit_mask, RegUpd.gpr_setV, State.store, RegUpd.wr_setV, hst,
    runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [RegUpd.mem_setV, RegUpd.mem_setV]
    by_cases hc : choose
    · simp only [hc, ite_true]
    · simp only [hc, ite_false, write_read_self]
  · rfl
  · rfl
  · rfl
  · simp only [RegUpd.v_setV_of_ne _ _ hq]

/-- The accumulators' loads, BITs and stores over one entry's 64 bytes. -/
def chunks (n : Nat) : List Instr := (List.range n).flatMap fun i =>
  [.ldrq .v21 .x16 (16 * i), .vop (.bsel .bit .v21 (acc i) .v20), .strq .v21 .x16 (16 * i)]

/-- After `chunks n`: the first `16 n` bytes at `dst` are `src`'s in the
memory `M` the accumulators were loaded from under the mask, and nothing
changes without it. -/
theorem chunks_ok (n : Nat) {s : State} {B : Addr} {dst src : Nat} {M : Mem} {choose : Prop} [Decidable choose]
    (hn : n ≤ 4) (hptr : s.gpr .x16 = off B dst) (hd : dst + 16 * n ≤ 2 ^ 64)
    (hm : s.v .v20 = if choose then BitVec.allOnes 128 else 0)
    (hv : ∀ i < n, s.v (acc i) = M.read (off B (src + 16 * i)) 16)
    (hld : ∀ i < n, InRegions (s.rd ++ s.wr) (off B (dst + 16 * i)) 16)
    (hw : ∀ i < n, InRegions s.wr (off B (dst + 16 * i)) 16) :
    WP isa (.block (chunks n)) s fun t => MKeep s t ∧
      if choose then Outside B dst (16 * n) s.mem t.mem ∧
        ∀ j < 16 * n, t.mem (off B (dst + j)) = M (off B (src + j))
      else t.mem = s.mem := by
  induction n with
  | zero =>
    refine WP.block_nil ⟨MKeep.refl s, ?_⟩
    split
    · exact ⟨Outside.refl _ _ _ _, fun _ h => by omega⟩
    · rfl
  | succ n ih =>
    rw [show chunks (n + 1) = chunks n ++ [.ldrq .v21 .x16 (16 * n),
      .vop (.bsel .bit .v21 (acc n) .v20), .strq .v21 .x16 (16 * n)] by
        simp [chunks, List.range_succ], WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) (by omega_using [hd]) (fun i hi => hv i (by omega_using [hi]))
      (fun i hi => hld i (by omega_using [hi])) (fun i hi => hw i (by omega_using [hi]))) fun t ⟨kt, ht⟩ => ?_
    have ptr : t.gpr .x16 + BitVec.ofNat 64 (16 * n) = off B (dst + 16 * n) := by
      rw [kt.gpr, hptr, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    refine WP.mono (chunk_ok (choose := choose) (acc_facts n (by omega_using [hn])).2.1 (by omega_using [hn])
      (by rw [kt.v .v20 (by decide)]; exact hm)
      (by rw [kt.rd, kt.wr, ptr]; exact hld n (by omega_using []))
      (by rw [kt.wr, ptr]; exact hw n (by omega_using []))) fun u ⟨hm', ku⟩ => ?_
    refine ⟨kt.trans ku, ?_⟩
    by_cases hc : choose
    · simp only [hc, ite_true] at ht hm' ⊢
      rw [ptr, kt.v _ (acc_facts n (by omega_using [hn])).2.1, hv n (by omega_using [])] at hm'
      have ho := write16_outside t.mem B (d := dst + 16 * n)
        (M.read (off B (src + 16 * n)) 16) (by omega_using [hd])
      rw [← hm'] at ho
      refine ⟨(ht.1.mono (by omega_using []) (by omega_using [])).trans
        (ho.mono (by omega_using []) (by omega_using [])), ?_⟩
      intro j hj
      by_cases hjn : j < 16 * n
      · rw [ho _ (by
          simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show dst + j < 2 ^ 64 by omega_using [hd, hj])]
          omega_using [hjn])]
        exact ht.2 j hjn
      · have hp : off B (dst + j) = off B (dst + 16 * n) + BitVec.ofNat 64 (j - 16 * n) := by
          rw [off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
          exact congrArg (fun z => B + BitVec.ofNat 64 z) (by omega_using [hjn])
        rw [hm', hp, write16_byte t.mem M _ _ (by omega_using [hj]), off,
          BitVec.add_assoc, ← BitVec.ofNat_add]
        exact congrArg (fun z => M (B + BitVec.ofNat 64 z)) (by omega_using [hjn])
    · simp only [hc, ite_false] at ht hm' ⊢
      exact hm'.trans ht

theorem storeRow_eq : storeRow =
    ([.vop (.cmeq .d2 .v20 .v23 .v22)] : List Instr) ++ chunks 4 ++ advance := rfl

/-- One entry: its 64 bytes take the accumulators' if its index is the digit. -/
theorem storeRow_ok {s : State} {B : Addr} {dst src j v : Nat} {M : Mem} (hj : j < 2 ^ 64) (hv : v < 2 ^ 64)
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j)) (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v))
    (h24 : s.v .v24 = dup2 1) (hptr : s.gpr .x16 = off B dst) (hd : dst + 64 ≤ 2 ^ 64)
    (hacc : ∀ i < 4, s.v (acc i) = M.read (off B (src + 16 * i)) 16)
    (hld : ∀ i < 4, InRegions (s.rd ++ s.wr) (off B (dst + 16 * i)) 16)
    (hw : ∀ i < 4, InRegions s.wr (off B (dst + 16 * i)) 16) :
    WP isa (.block storeRow) s fun t =>
      ((if j = v then Outside B dst 64 s.mem t.mem ∧ ∀ k < 64, t.mem (off B (dst + k)) = M (off B (src + k))
        else t.mem = s.mem) ∧
      t.gpr .x16 = s.gpr .x16 + s.gpr .x6 ∧ t.v .v23 = dup2 (BitVec.ofNat 64 (j + 1)) ∧
      t.v .v22 = s.v .v22 ∧ t.v .v24 = s.v .v24 ∧ ∀ i < 4, t.v (acc i) = s.v (acc i)) ∧ Keep [.x16] s t := by
  refine WP.keep [.x16] ?_ (by decide) (by decide) (by decide +kernel)
  rw [storeRow_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (compare_ok hj hv h23 h22) fun a ⟨ha, ka⟩ => ?_
  have hav : ∀ i < 4, a.v (acc i) = s.v (acc i) := fun i hi =>
    ka.v _ (by simpa only [List.mem_singleton] using (acc_facts i hi).1)
  refine WP.mono (chunks_ok (choose := j = v) (M := M) (B := B) (src := src) 4 (by decide) (by rw [ka.gpr]; exact hptr) hd ha
    (fun i hi => by rw [hav i hi]; exact hacc i hi)
    (fun i hi => by rw [ka.rd, ka.wr]; exact hld i hi) (fun i hi => by rw [ka.wr]; exact hw i hi))
    fun b ⟨kb, hb⟩ => ?_
  refine WP.mono (advance_ok (j := j) (by rw [kb.v _ (by decide), ka.v _ (by decide)]; exact h23)
    (by rw [kb.v _ (by decide), ka.v _ (by decide)]; exact h24)) fun t ht => ?_
  subst t
  rw [ka.mem] at hb
  refine ⟨?_, ?_, RegUpd.v_setV_self _ _ _, ?_, ?_, ?_⟩
  · simpa only [RegUpd.mem_setV, RegUpd.mem_write] using hb
  · simp only [RegUpd.gpr_setV, RegUpd.gpr_write_self, BitVec.setWidth_eq, kb.gpr, ka.gpr]
  · rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_write, kb.v _ (by decide), ka.v _ (by decide)]
  · rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_write, kb.v _ (by decide), ka.v _ (by decide)]
  · intro i hi
    have hn : acc i ≠ .v23 ∧ acc i ≠ .v21 := (by decide : ∀ i < 4, acc i ≠ .v23 ∧ acc i ≠ .v21) i hi
    rw [RegUpd.v_setV_of_ne _ _ hn.1, RegUpd.v_write, kb.v _ hn.2, hav i hi]

/-- After `j` entries: entry `v`'s 64 bytes are the source's once passed. -/
structure RowInv (s : State) (B : Addr) (base stride src v j : Nat) (t : State) : Prop where
  keep : Keep [.x14, .x16] s t
  ptr : t.gpr .x16 = off B (base + stride * j)
  index : t.v .v23 = dup2 (BitVec.ofNat 64 j)
  digit : t.v .v22 = dup2 (BitVec.ofNat 64 v)
  one : t.v .v24 = dup2 1
  accs : ∀ i < 4, t.v (acc i) = s.v (acc i)
  mem : if v < j then Outside B (base + stride * v) 64 s.mem t.mem ∧
      ∀ k < 64, t.mem (off B (base + stride * v + k)) = s.mem (off B (src + k))
    else t.mem = s.mem

theorem rowStep_ok {s t : State} {B : Addr} {base stride src v j n : Nat} (hn : n ≤ 32) (hj : j < n)
    (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride) (hI : RowInv s B base stride src v j t)
    (hacc : ∀ i < 4, s.v (acc i) = s.mem.read (off B (src + 16 * i)) 16)
    (hfit : ∀ j < n, base + stride * j + 64 ≤ 2 ^ 64)
    (hld : ∀ j < n, ∀ i < 4, InRegions (s.rd ++ s.wr) (off B (base + stride * j + 16 * i)) 16)
    (hw : ∀ j < n, ∀ i < 4, InRegions s.wr (off B (base + stride * j + 16 * i)) 16) :
    WP isa (.block (storeRow ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      RowInv s B base stride src v (j + 1) u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff]
  refine WP.mono (storeRow_ok (M := s.mem) (src := src) (by omega_using [hj, hn]) (by omega_using [hv])
    hI.index hI.digit hI.one hI.ptr (hfit j hj) (fun i hi => (hI.accs i hi).trans (hacc i hi))
    (fun i hi => by rw [hI.keep.rd, hI.keep.wr]; exact hld j hj i hi)
    (fun i hi => by rw [hI.keep.wr]; exact hw j hj i hi)) fun a ⟨⟨hm, hp, h23, h22, h24, hacc'⟩, ka⟩ => ?_
  refine WP.mono (decVector_ok a) fun u ⟨⟨hu, hum, huv⟩, ku⟩ => ?_
  refine ⟨⟨((hI.keep.trans ka).trans ku).mono (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hu.trans (congrArg (· - BitVec.ofNat 64 1) (ka.gpr .x14 (by decide)))⟩
  · rw [ku.gpr .x16 (by decide), hp, hI.ptr, hI.keep.gpr .x6 (by decide), hs,
      BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  · rw [huv, h23]
  · rw [huv, h22, hI.digit]
  · rw [huv, h24, hI.one]
  · intro i hi
    rw [huv, hacc' i hi, hI.accs i hi]
  · rw [hum]
    have hIm := hI.mem
    by_cases he : j = v
    · subst j
      simp only [Nat.lt_irrefl, ite_false] at hIm
      simp only [ite_true, Nat.lt_succ_self] at hm ⊢
      rw [hIm] at hm
      exact hm
    · have heq : v < j + 1 ↔ v < j := by omega_using [he]
      simp only [he, ite_false] at hm
      simp only [heq]
      rw [hm]
      exact hIm

/-- The eight entries' rows: entry `v`'s 64 bytes at this tile become the
source's, and nothing else changes. -/
theorem rows_ok {s : State} {B : Addr} {base stride src v n : Nat} (hn : n ≤ 32) (hv : v < n)
    (hs : s.gpr .x6 = BitVec.ofNat 64 stride) (hc : s.gpr .x14 = BitVec.ofNat 64 n)
    (hptr : s.gpr .x16 = off B base) (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 0))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1)
    (hacc : ∀ i < 4, s.v (acc i) = s.mem.read (off B (src + 16 * i)) 16)
    (hfit : ∀ j < n, base + stride * j + 64 ≤ 2 ^ 64)
    (hld : ∀ j < n, ∀ i < 4, InRegions (s.rd ++ s.wr) (off B (base + stride * j + 16 * i)) 16)
    (hw : ∀ j < n, ∀ i < 4, InRegions s.wr (off B (base + stride * j + 16 * i)) 16) :
    WP isa (countLoop .x14 storeRow) s fun t =>
      Keep [.x14, .x16] s t ∧ t.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ t.v .v24 = dup2 1 ∧
      Outside B (base + stride * v) 64 s.mem t.mem ∧
      ∀ k < 64, t.mem (off B (base + stride * v + k)) = s.mem (off B (src + k)) := by
  unfold countLoop
  refine WP.mono (wp_countdown (by omega_using [hn]) (Nat.zero_lt_of_lt hv)
    (fun j => RowInv s B base stride src v j)
    (fun j hj t hI _ => rowStep_ok hn hj (Nat.lt_of_lt_of_le hv hn) hs hI hacc hfit hld hw)
    ⟨Keep.refl _ _, by rw [hptr, Nat.mul_zero, Nat.add_zero], h23, h22, h24, fun _ _ => rfl,
      by simp only [Nat.not_lt_zero, ite_false]⟩ hc) fun t hI => ?_
  have hm := hI.mem
  simp only [hv, ite_true] at hm
  exact ⟨hI.keep, hI.digit, hI.one, hm.1, hm.2⟩

/-- The accumulators' loads from the source's 64 bytes. -/
def loads (n : Nat) : List Instr := (List.range n).map fun i => .ldrq (acc i) .x17 (16 * i)

theorem load_ok {s : State} {r : VReg} {i : Nat} (hi : i < 4)
    (hld : InRegions (s.rd ++ s.wr) (s.gpr .x17 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block [.ldrq r .x17 (16 * i)]) s fun t =>
      t = s.setV r (s.mem.read (s.gpr .x17 + BitVec.ofNat 64 (16 * i)) 16) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, addr, show 16 * i % 16 = 0 by omega_using [],
    show 16 * i < 4096 * 16 by omega_using [hi], and_self, ite_true, Option.bind_some,
    State.load, hld, Option.map_some, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']

theorem loads_ok (n : Nat) {s : State} (hn : n ≤ 4)
    (hld : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr .x17 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block (loads n)) s fun t =>
      (∀ i < n, t.v (acc i) = s.mem.read (s.gpr .x17 + BitVec.ofNat 64 (16 * i)) 16) ∧ VKeep accs s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => by omega, ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | succ n ih =>
    rw [show loads (n + 1) = loads n ++ [.ldrq (acc n) .x17 (16 * n)] by
      simp [loads, List.range_succ], WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) (fun i hi => hld i (by omega_using [hi]))) fun t ⟨hv, kt⟩ => ?_
    refine WP.mono (load_ok (r := acc n) (by omega_using [hn])
      (by rw [kt.rd, kt.wr, kt.gpr]; exact hld n (by omega_using []))) fun u hu => ?_
    subst u
    refine ⟨fun i hi => ?_, kt.trans ((VKeep.setV _ _ _).mono (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact (by decide : ∀ i < 4, acc i ∈ accs) n (by omega_using [hn])))|>.mono (by simp)⟩
    by_cases he : i = n
    · subst i
      rw [RegUpd.v_setV_self, kt.mem, kt.gpr]
    · rw [RegUpd.v_setV_of_ne _ _ (acc_ne i (by omega_using [hi, hn]) n (by omega_using [hn]) he),
        hv i (by omega_using [hi, he])]

theorem blockHead8_ok {s : State} {P : Addr} {w b : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P w mi X Xc) (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b)) :
    WP isa (.block (blockHead 8)) s fun t =>
      (t.gpr .x16 = off P (slot w 8 + 64 * b) ∧ t.gpr .x14 = BitVec.ofNat 64 8 ∧
       t.v = (s.setV .v23 0).v ∧ t.mem = s.mem) ∧ Keep [.x16, .x3, .x14] s t := by
  have hp' : off P (slot w Crt.aT + 64 * b) - off P (slot w Crt.aT) = BitVec.ofNat 64 (64 * b) := by
    rw [off, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.add_sub_cancel_left _ _
  refine WP.keep _ ?_ rfl rfl rfl
  brun [blockHead, hc.good.x0, hdr_enc (sArr_lt (show Crt.aT < 8 by decide)),
    hdr_enc (show Crt.sTab < 32 by decide), hc.ld (i := sArr Crt.aT) (by decide),
    hc.ld (i := Crt.sTab) (by decide), hc.good.hdr.harr Crt.aT (by decide), ht, hp, hp',
    exec_zeroVector, RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV]
  refine ⟨BitVec.add_comm _ _ |>.trans (off_add P (slot w 8) (64 * b)), ?_⟩
  simp only [State.setV, RegUpd.v_write]

/-- One tile of the store: its head, and the eight entries' rows. -/
def storeTile : Prog isa := .seq (.block (blockHead 8 ++ loads 4)) (countLoop .x14 storeRow)

theorem slot_ent (w v : Nat) : slot w 8 + 8 * (w + 2) * v = slot w (8 + v) := by
  simp only [slot, Nat.add_mul, Nat.mul_comm v, Nat.add_assoc]

/-- A tile's head: the entries' pointer and count, and the source's 64
bytes in the accumulators. -/
theorem storeHead_ok {s : State} {P : Addr} {w b : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P w mi X Xc) (hb : 8 * b + 8 ≤ w)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b)) :
    WP isa (.block (blockHead 8 ++ loads 4)) s fun a =>
      a.gpr .x16 = off P (slot w 8 + 64 * b) ∧ a.gpr .x14 = BitVec.ofNat 64 8 ∧ a.mem = s.mem ∧
      (∀ r, r ∉ accs → a.v r = (s.setV .v23 0).v r) ∧
      (∀ i < 4, a.v (acc i) = s.mem.read (off P (slot w Crt.aT + 64 * b + 16 * i)) 16) ∧
      Keep [.x16, .x3, .x14] s a := by
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  rw [WP.block_append_iff]
  refine WP.mono (blockHead8_ok hc ht hp) fun u ⟨⟨h16, h14, huv, hum⟩, ku⟩ => ?_
  have hu17 : u.gpr .x17 = off P (slot w Crt.aT + 64 * b) := (ku.gpr .x17 (by decide)).trans hp
  refine WP.mono (loads_ok 4 (by decide) (fun i hi => by
    rw [ku.rd, ku.wr, hu17, off_add]
    exact (hc.good.scr.region (d := slot w Crt.aT + 64 * b + 16 * i) (n := 16)
      (by omega_using [hb, hi, hT]) (by decide)).imp fun r hr => ⟨List.mem_append_right _ hr.1, hr.2⟩))
    fun a ⟨hacc, ka⟩ => ?_
  have hkeep : Keep [] u a := ⟨fun r _ => congrFun ka.gpr r, ka.rd, ka.wr, ka.sp,
    fun r hr => congrArg (fun x : BitVec 128 => x.extractLsb' 0 64)
      (ka.v r ((by decide : ∀ r ∈ preservedV, r ∉ accs) r hr))⟩
  exact ⟨by rw [ka.gpr]; exact h16, by rw [ka.gpr]; exact h14, ka.mem.trans hum,
    fun r hr => (ka.v r hr).trans (congrFun huv r),
    fun i hi => by rw [hacc i hi, hum, hu17, off_add], (ku.trans hkeep).mono (by decide)⟩

theorem storeTile_ok {s : State} {P : Addr} {w b v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P w mi X Xc) (hv : v < 8) (hb : 8 * b + 8 ≤ w)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b))
    (hs : s.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2)))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1) :
    WP isa storeTile s fun t =>
      Keep [.x16, .x3, .x14] s t ∧ Outside P (slot w (8 + v) + 64 * b) 64 s.mem t.mem ∧
      t.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ t.v .v24 = dup2 1 ∧
      ∀ k < 64, t.mem (off P (slot w (8 + v) + 64 * b + k)) = s.mem (off P (slot w Crt.aT + 64 * b + k)) := by
  have hn := hc.scrT.nowrap
  have he : slot w 8 + 64 * b + 8 * (w + 2) * v = slot w (8 + v) + 64 * b := by
    have := slot_ent w v; omega_using [this]
  unfold storeTile
  apply WP.seq
  refine WP.mono (storeHead_ok hc hb ht hp) fun a ⟨h16, h14, ham, hav, hacc, ka⟩ => ?_
  refine WP.mono (rows_ok (B := P) (base := slot w 8 + 64 * b) (stride := 8 * (w + 2))
    (src := slot w Crt.aT + 64 * b) (v := v) (n := 8) (by decide) hv
    (by rw [ka.gpr .x6 (by decide)]; exact hs) h14 h16
    (by rw [hav _ (by decide), RegUpd.v_setV_self]; rfl)
    (by rw [hav _ (by decide), RegUpd.v_setV_of_ne _ _ (by decide)]; exact h22)
    (by rw [hav _ (by decide), RegUpd.v_setV_of_ne _ _ (by decide)]; exact h24)
    (fun i hi => by rw [hacc i hi, ham])
    (fun j hj => by
      have hE := ent_le w (n := 16) (show j < 16 by omega_using [hj])
      have := slot_ent w j
      omega_using [hb, hE, this, hn])
    (fun j hj i hi => by
      rw [ka.rd, ka.wr]
      exact tableTile_ld hc hb (show j < 16 by omega_using [hj]) hi)
    (fun j hj i hi => by
      rw [ka.wr]
      have hE := ent_le w (n := 16) (show j < 16 by omega_using [hj])
      have := slot_ent w j
      exact hc.scrT.region (by omega_using [hb, hi, hE, this]) (by decide)))
    fun t ⟨kt, h22', h24', ho, hbytes⟩ => ?_
  rw [he, ham] at ho
  refine ⟨(ka.trans kt).mono (by decide), ho, h22', h24', fun k hk => ?_⟩
  have := hbytes k hk
  rwa [he, ham] at this

/-- After `j` tiles: entry `v`'s first `64 j` bytes are `[aT]`'s. -/
structure StoreInv (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc v j : Nat) (t : State) : Prop where
  ctx : CExpCtx t P w mi X Xc
  tab : word t.mem P (8 * Crt.sTab) = off P (slot w 8)
  stride : t.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2))
  ptr : t.gpr .x17 = off P (slot w Crt.aT + 64 * j)
  digit : t.v .v22 = dup2 (BitVec.ofNat 64 v)
  one : t.v .v24 = dup2 1
  frame : Outside P (slot w (8 + v)) (64 * j) s.mem t.mem
  bytes : ∀ k < 64 * j, t.mem (off P (slot w (8 + v) + k)) = s.mem (off P (slot w Crt.aT + k))
  keep : Keep mmRegs s t

def storeStep : Prog isa := .seq storeTile (.block [.addImm .x .x17 .x17 64, .subImm .x .x13 .x13 1])

/-- The loop's body as the code has it. -/
def storeRaw : Prog isa :=
  .seq (.block (blockHead 8 ++ loads 4))
    (.seq (countLoop .x14 storeRow) (.block [.addImm .x .x17 .x17 64, .subImm .x .x13 .x13 1]))

theorem storeRaw_wp (s : State) (Q : State → Prop) : WP isa storeRaw s Q ↔ WP isa storeStep s Q := by
  unfold storeRaw storeStep storeTile
  simp only [WP.seq_iff (M := isa)]

theorem store_eq : store = .seq (.block setup) (.loop storeRaw (.nonzero .x .x13)) := rfl

theorem storeStep_ok {s t : State} {P : Addr} {w v j : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hv : v < 8) (hj : 8 * j + 8 ≤ w) (hI : StoreInv s P w mi X Xc v j t) :
    WP isa storeStep t fun u => StoreInv s P w mi X Xc v (j + 1) u ∧
      u.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hI.ctx.scrT.nowrap
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  have hE := ent_le w (n := 16) (show v < 16 by omega_using [hv])
  have hE0 := slot_mono w (show 8 ≤ 8 + v by omega_using [])
  have hsep := slot_mono w (show Crt.aT + 1 ≤ 8 by decide)
  have hsucc := slot_succ w Crt.aT
  unfold storeStep
  apply WP.seq
  refine WP.mono (storeTile_ok hI.ctx hv hj hI.tab hI.ptr hI.stride hI.digit hI.one)
    fun a ⟨ka, ho, h22, h24, hb⟩ => ?_
  have hcopy : ∀ k < 64, a.mem (off P (slot w (8 + v) + 64 * j + k)) =
      s.mem (off P (slot w Crt.aT + 64 * j + k)) := by
    intro k hk
    rw [hb k hk]
    exact hI.frame _ (Or.inl (by
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show slot w Crt.aT + 64 * j + k < 2 ^ 64 by omega_using [hj, hn, hT, hk])]
      omega_using [hj, hk, hsep, hsucc, hE0]))
  have copied := copy_append (by omega_using [hj, hn, hE]) hI.frame ho hI.bytes hcopy
  refine WP.mono (tileAdvance_ok a) fun u ⟨⟨hp, hc, hm, hvec⟩, ku⟩ => ?_
  have localFrame : Frm P (crtExpRanges w) t.mem u.mem := by
    rw [hm]
    exact Frm.of_outside (ho.mono (o' := slot w 8) (n' := tabBytes w)
      (by omega_using [hE0]) (by omega_using [hj, hE])) (by simp [crtExpRanges])
  have keep := (ka.trans ku).mono (rs' := mmRegs) (by decide)
  refine ⟨⟨hI.ctx.of_frm localFrame keep.wr (keep.gpr .x0 (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (hI.keep.trans keep).mono (by decide)⟩, ?_⟩
  · rw [hm, ho.word (Or.inl (by have := hdr_lt_slot w 8 (show Crt.sTab < 32 by decide); omega_using [this, hE0]))
      (by decide)]
    exact hI.tab
  · rw [ku.gpr .x6 (by decide), ka.gpr .x6 (by decide)]
    exact hI.stride
  · rw [hp, ka.gpr .x17 (by decide), hI.ptr, off_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  · rw [hvec]; exact h22
  · rw [hvec]; exact h24
  · rw [hm, Nat.mul_add, Nat.mul_one]
    exact copied.1
  · simpa only [hm, Nat.mul_add, Nat.mul_one] using copied.2
  · rw [hc, ka.gpr .x13 (by decide)]

/-- The masked store: entry `v` of the first eight takes `[aT]`, for the
secret digit `v` in `sNib`, and nothing else changes. -/
theorem store_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P w mi X Xc) (hw : 8 ≤ w) (hw' : w < 2 ^ 30) (hd : w % 8 = 0) (hv : v < 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hNib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa store s fun t => CExpCtx t P w mi X Xc ∧
      wv t.mem P (slot w (8 + v)) w = wv s.mem P (slot w Crt.aT) w ∧
      Outside P (slot w (8 + v)) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hcount : 64 * (w / 8) = 8 * w := by omega_using [hd]
  rw [store_eq]
  apply WP.seq
  refine WP.mono (setup_ok hc hw' hNib) fun u ⟨⟨h6, h13, h17, h22, h24, hm⟩, ku⟩ => ?_
  have ctx : CExpCtx u P w mi X Xc := hc.of_win
    (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have h0 : StoreInv u P w mi X Xc v 0 u := ⟨ctx, by rw [hm]; exact ht,
    h6, by simpa using h17, h22, h24, Outside.refl _ _ _ _,
    fun k hk => by omega, Keep.refl _ _⟩
  refine WP.mono (wp_countdown (by omega_using [hw']) (by omega_using [hw])
    (fun j => StoreInv u P w mi X Xc v j)
    (fun j hj t hI _ => (storeRaw_wp _ _).mpr (storeStep_ok hv (by omega_using [hj]) hI)) h0 h13)
    fun t hI => ?_
  refine ⟨hI.ctx, ?_, ?_, (ku.trans hI.keep).mono (by decide)⟩
  · apply wv_copy
    simpa only [hcount, hm] using hI.bytes
  · simpa only [hcount, hm] using hI.frame

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! # One digit of the shared exponentiation: a bucket times the base's power

The secret digit's bucket is read by the scan of every entry and written
back under a mask; the public digit's is read and written directly. Each
lemma says which bucket becomes its product with `[aXc]`, and that the
other buckets, the arrays and the header's slots are as they were. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower

/-! ## What each kind of change keeps -/

/-- The header's slots through a selection. -/
theorem sel_hdr {m m' : Mem} {P : Addr} {wx : Nat} (hf : Frm P (selRanges wx) m m') {k : Nat} (hk : k < 32)
    (h1 : k ≠ Crt.sEnt) (h2 : k ≠ Crt.sJ) : word m' P (8 * k) = word m P (8 * k) :=
  hf.word_eq (fun r hr => by
    have := hdr_lt_slot wx Crt.aT hk
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only; omega_arith
    · simp only [Crt.sEnt, sFn] at h1 ⊢; omega_arith
    · simp only [Crt.sJ, sFn] at h2 ⊢; omega_arith) (by omega_arith)

/-- The table's entries through a window's changes. -/
theorem win_ent {m m' : Mem} {P : Addr} {wx : Nat} (hf : Frm P (crtWinRanges wx) m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 16) :
    wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
  hf.wv_eq (fun r hr => by have := crtWinRanges_ent wx j r hr; omega_arith)
    (by have := ent_le wx hj; omega_arith)

/-- An array a window does not use, through its changes. -/
theorem win_arr {m m' : Mem} {P : Addr} {wx : Nat} (hf : Frm P (crtWinRanges wx) m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp)
    (h3 : j ≠ aY) (h4 : j ≠ Crt.aT) : wv m' P (slot wx j) wx = wv m P (slot wx j) wx :=
  hf.wv_eq (fun r hr => by
    have := crtExpRanges_arr wx hj h1 h2 h3 h4 16 r (crtWinRanges_sub wx r hr); omega_arith)
    (by have := slot_le (w := wx) hj; omega_arith)

/-- The table's entries through changes to arrays. -/
theorem arr_ent {m m' : Mem} {P : Addr} {wx : Nat} {js : List Nat} (hf : Arrays P wx js m m')
    (hjs : ∀ a ∈ js, a < 8) (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 16) :
    wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
  hf.wv_eq (fun a ha => Or.inr (by
    have := slot_le (w := wx) (hjs a ha)
    have := slot_mono wx (show 8 ≤ 8 + j by omega_arith)
    omega_arith)) (by have := ent_le wx hj; omega_arith)

/-- Another entry through a store to one. -/
theorem ent_ent {m m' : Mem} {P : Addr} {wx v : Nat} (hf : Outside P (slot wx (8 + v)) (8 * wx) m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 16) (hjv : j ≠ v) :
    wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
  hf.wv (by have := slot_sep (w := wx) (show 8 + j ≠ 8 + v by omega_arith); omega_arith)
    (by have := ent_le wx hj; omega_arith)

/-- An array through a store to an entry. -/
theorem ent_arr {m m' : Mem} {P : Addr} {wx v : Nat} (hf : Outside P (slot wx (8 + v)) (8 * wx) m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 8) :
    wv m' P (slot wx j) wx = wv m P (slot wx j) wx :=
  hf.wv (Or.inl (by
    have := slot_le (w := wx) hj
    have := slot_mono wx (show 8 ≤ 8 + v by omega_arith)
    omega_arith)) (by have := slot_le (w := wx) hj; omega_arith)

/-- A header slot through a store to an entry. -/
theorem ent_hdr {m m' : Mem} {P : Addr} {wx v : Nat} (hf : Outside P (slot wx (8 + v)) (8 * wx) m m')
    {k : Nat} (hk : k < 32) : word m' P (8 * k) = word m P (8 * k) :=
  hf.word (Or.inl (hdr_lt_slot wx (8 + v) hk)) (by omega_arith)

/-- A store to an entry is within the workspace's mutable region. -/
theorem ent_work {m m' : Mem} {P : Addr} {wx v : Nat} (hf : Outside P (slot wx (8 + v)) (8 * wx) m m')
    (hv : v < 16) : Frm P (workRanges wx) m m' := by
  intro x hx
  apply hf x
  obtain h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  have := ent_le wx hv
  have := slot_mono wx (show 8 ≤ 8 + v by omega_arith)
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  omega_arith

/-- A window's changes are within the workspace's mutable region. -/
theorem win_work {m m' : Mem} {P : Addr} {wx : Nat} (hf : Frm P (crtWinRanges wx) m m') :
    Frm P (workRanges wx) m m' := by
  intro x hx
  apply hf x
  intro r hr
  obtain ho := crtWinRanges_ok wx r hr
  obtain h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  omega_arith

/-- A store to one of the header's slots for the functions' own use. -/
theorem fn_outside (m : Mem) (P : Addr) {i : Nat} (v : BitVec 64) (hi : 17 ≤ i) (hi' : i < 32) :
    Outside P 136 120 m (m.writeW (off P (8 * i)) v) :=
  (writeW_outside m P v (by omega_arith)).mono (by omega_arith) (by omega_arith)

/-- The context through changes to the header's slots for the functions' own use. -/
theorem ctx_of_fn {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat}
    (hc : CExpCtx s P wx minv N Xc) (ho : Outside P 136 120 s.mem t.mem) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = s.gpr .x0) : CExpCtx t P wx minv N Xc := by
  have hn := hc.scrT.nowrap
  obtain h256 : 256 ≤ slot wx 0 := by unfold slot hdrBytes; omega_arith
  obtain hh : ∀ i < 17, word t.mem P (8 * i) = word s.mem P (8 * i) := fun i hi =>
    ho.word (Or.inl (by omega_arith)) (by omega_arith)
  obtain ha : ∀ j < 8, wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx := fun j hj =>
    ho.wv (Or.inr (by have := slot_mono wx (show 0 ≤ j by omega_arith); omega_arith))
      (by have := slot_le (w := wx) hj; omega_arith)
  exact ⟨⟨hc.good.scr.congr hwr, h0.trans hc.good.x0,
    ⟨(hh _ (by decide)).trans hc.good.hdr.hw, (hh _ (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩, hc.scrT.congr hwr,
    (ha _ (by decide)).trans hc.n,
    by rw [ho.word (Or.inr (by have := slot_mono wx (show 0 ≤ aN by decide); omega_arith))
      (by have := slot_le (w := wx) (show aN < 8 by decide); omega_arith)]; exact hc.inv,
    (ha _ (by decide)).trans hc.x⟩

/-- The table's entries through changes to those slots. -/
theorem fn_ent {m m' : Mem} {P : Addr} {wx : Nat} (ho : Outside P 136 120 m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 16) :
    wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
  ho.wv (Or.inr (by
    have : 256 ≤ slot wx 0 := by unfold slot hdrBytes; omega_arith
    have := slot_mono wx (show 0 ≤ 8 + j by omega_arith)
    omega_arith)) (by have := ent_le wx hj; omega_arith)

/-- An array through changes to those slots. -/
theorem fn_arr {m m' : Mem} {P : Addr} {wx : Nat} (ho : Outside P 136 120 m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 8) :
    wv m' P (slot wx j) wx = wv m P (slot wx j) wx :=
  ho.wv (Or.inr (by
    have : 256 ≤ slot wx 0 := by unfold slot hdrBytes; omega_arith
    have := slot_mono wx (show 0 ≤ j by omega_arith)
    omega_arith)) (by have := slot_le (w := wx) hj; omega_arith)

/-- Changes to those slots are within the workspace's mutable region. -/
theorem fn_work {m m' : Mem} {P : Addr} {wx : Nat} (ho : Outside P 136 120 m m') :
    Frm P (workRanges wx) m m' := by
  intro x hx
  apply ho x
  obtain h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  omega_arith

/-! ## The secret digit's bucket -/

theorem secretDigit_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc V : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hV : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64) :
    WP isa (.block secretDigit) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (V % 8)) ∧ Keep [.x3, .x4] s t := by
  refine WP.keep [.x3, .x4] ?_ rfl rfl rfl
  brun [secretDigit, hc.good.x0, hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show Crt.sNib < 32 by decide),
    hc.ld (i := Crt.sV) (by decide), hc.st (i := Crt.sNib) (by decide), hV]
  exact congrArg (s.mem.writeW _) (BlockedRedc.mask7_ofNat hV')

/-- The secret digit `V mod 8`'s bucket becomes its product with `[aXc]`:
by the scan of every entry, the multiplication and the masked store. -/
theorem secretBucket_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc V : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 8 ≤ wx) (hw' : wx < 2 ^ 30) (hd : wx % 8 = 0)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hV : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64)
    (hA : Xc < N) :
    WP isa (seqs [.block secretDigit, Crt.select, M.mm Crt.aT Crt.aT Crt.aXc, store]) s fun t =>
      CExpCtx t P wx minv N Xc ∧ wv t.mem P (slot wx (8 + V % 8)) wx < N ∧
      wv t.mem P (slot wx (8 + V % 8)) wx * 2 ^ (64 * wx) % N =
        wv s.mem P (slot wx (8 + V % 8)) wx * Xc % N ∧
      (∀ j < 16, j ≠ V % 8 → wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx) ∧
      (∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT →
        wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  obtain hv8 : V % 8 < 8 := Nat.mod_lt _ (by decide)
  obtain hv16 : V % 8 < 16 := by omega_using [hv8]
  simp only [seqs]
  refine WP.seq (WP.mono (secretDigit_ok hc hV hV') fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain o₁ := writeW_outside s.mem P (d := 8 * Crt.sNib) (BitVec.ofNat 64 (V % 8)) (by decide)
  rw [← hm₁] at o₁
  obtain f₁ : Frm P (crtWinRanges wx) s.mem s₁.mem := Frm.of_outside o₁ (by simp [crtWinRanges])
  obtain hc₁ := hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide))
  obtain hh₁ : ∀ k < 32, k ≠ Crt.sNib → word s₁.mem P (8 * k) = word s.mem P (8 * k) := fun k hk h => by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h)]
  refine WP.seq (WP.mono (WindowVector.select_ok (Or.inl rfl)
    (fun hu tab nib => tabSel_ok hu (by omega_using [hw]) hw' hv16 tab nib) hc₁ hw' hv16
    (by rw [hh₁ _ (by decide) (by decide)]; exact ht) (by rw [hm₁, word_writeW_self]))
    fun s₂ ⟨hc₂, hT₂, f₂, k₂⟩ => ?_)
  obtain f₂' : Frm P (crtWinRanges wx) s₁.mem s₂.mem := f₂.mono (selRanges_sub wx)
  refine WP.seq (WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc₂.good (Nat.le_refl _)
    (by omega_using [hw]) (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc₂.inv (by rw [hc₂.n, hc₂.x]; exact hA)) fun s₃ ⟨_, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [hc₂.n] at hlt₃ hm₃
  obtain f₃ : Frm P (crtWinRanges wx) s₂.mem s₃.mem := Frm.of_arrays ha₃ (by simp [crtWinRanges])
  obtain hc₃ := hc₂.of_win f₃ k₃.wr (k₃.gpr .x0 (by decide))
  obtain tab₃ : word s₃.mem P (8 * Crt.sTab) = off P (slot wx 8) := by
    rw [ha₃.hslot (by decide), sel_hdr f₂ (by decide) (by decide) (by decide), hh₁ _ (by decide) (by decide)]
    exact ht
  obtain nib₃ : word s₃.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (V % 8) := by
    rw [ha₃.hslot (by decide), sel_hdr f₂ (by decide) (by decide) (by decide), hm₁, word_writeW_self]
  refine WP.mono (store_ok hc₃ hw hw' hd hv8 tab₃ nib₃) fun t ⟨hct, hE, o₄, k₄⟩ => ?_
  obtain f03 : Frm P (crtWinRanges wx) s.mem s₃.mem := (f₁.trans f₂').trans f₃
  refine ⟨hct, by rw [hE]; exact hlt₃, ?_, fun j hj hjv => ?_, fun j hj h1 h2 h3 h4 => ?_,
    fun k hk h1 h2 h3 => ?_, (win_work f03).trans (ent_work o₄ hv16),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · rw [hE, hm₃, hT₂, hc₂.x, win_ent f₁ hn hv16]
  · rw [ent_ent o₄ hn hj hjv, win_ent f03 hn hj]
  · rw [ent_arr o₄ hn hj, win_arr f03 hn hj h1 h2 h3 h4]
  · rw [ent_hdr o₄ hk, ha₃.hslot hk, sel_hdr f₂ hk h2 h3, hh₁ k hk h1]

/-! ## The public digit's bucket -/

/-- `T_v := [aT]` for the public `v` in `sNib`. -/
theorem put_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc v : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa put s fun t => CExpCtx t P wx minv N Xc ∧
      wv t.mem P (slot wx (8 + v)) wx = wv s.mem P (slot wx Crt.aT) wx ∧
      Outside P (slot wx (8 + v)) (8 * wx) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  obtain hE := ent_le wx hv
  obtain hE0 := slot_mono wx (show 8 ≤ 8 + v by omega_arith)
  have hz := hc.scrT.nowrap
  unfold put
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (PublicPower.selectHead_ok hc hw' hv ht hn) fun u ⟨⟨h12, h16, h17, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun a => a.gpr .x16 = u.gpr .x17 ∧
    a.gpr .x17 = u.gpr .x16 ∧ a.mem = u.mem) (by brun []) rfl rfl rfl) fun a ⟨⟨a16, a17, am⟩, ka⟩ => ?_
  obtain hs := hc.scrT.congr (hk.trans ka).wr
  refine WP.mono (copyWords_ok (S := P) (D := P) (eS := slot wx Crt.aT) (eD := slot wx (8 + v))
    (a16.trans h17) (a17.trans h16) ((ka.gpr .x12 (by decide)).trans h12) (by omega_using [hw])
    (by omega_using [hw']) (by omega_using [hE, hz])
    (fun i hi => hs.ld (by omega_using [hT, hi])) (fun i hi => hs.st (by omega_using [hE, hi]))
    (fun i hi b hb => by rw [ofs_off P (by omega_using [hT, hz, hi, hb])]; omega_using [hT, hE0, hi, hb]))
    fun t ⟨hval, _, hf, _, _, hkt⟩ => ?_
  rw [am, hm] at hf hval
  obtain k := ((hk.trans ka).trans hkt).mono (rs' := mmRegs) (by decide)
  exact ⟨hc.of_frm (Frm.of_outside (hf.mono (o' := slot wx 8) (n' := tabBytes wx) hE0 (by omega_using [hE]))
    (by simp [crtExpRanges])) k.wr (k.gpr .x0 (by decide)), hval, hf, k⟩

theorem publicDigit_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc Q : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hQ : word s.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 Q) (hQ' : Q < 2 ^ 64) :
    WP isa (.block publicDigit) s fun t =>
      (t.gpr .x3 = BitVec.ofNat 64 (Q % 8) ∧ t.mem = s.mem) ∧ Keep [.x3, .x4] s t := by
  refine WP.keep [.x3, .x4] ?_ rfl rfl rfl
  brun [publicDigit, hc.good.x0, hdr_enc (show Crt.sMaskX < 32 by decide), hc.ld (i := Crt.sMaskX) (by decide), hQ]
  exact BlockedRedc.mask7_ofNat hQ'

/-- The public digit `d`'s bucket, entry `8 + d`, becomes its product with
`[aXc]`, read and written directly. -/
theorem publicBucket_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc d : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hd : d < 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8)) (h3 : s.gpr .x3 = BitVec.ofNat 64 d)
    (hA : Xc < N) :
    WP isa (publicBucket M.mm) s fun t =>
      CExpCtx t P wx minv N Xc ∧ wv t.mem P (slot wx (8 + (8 + d))) wx < N ∧
      wv t.mem P (slot wx (8 + (8 + d))) wx * 2 ^ (64 * wx) % N =
        wv s.mem P (slot wx (8 + (8 + d))) wx * Xc % N ∧
      (∀ j < 16, j ≠ 8 + d → wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx) ∧
      (∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT →
        wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  obtain hv16 : 8 + d < 16 := by omega_using [hd]
  obtain hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  unfold publicBucket
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off P (8 * Crt.sNib))
      (BitVec.ofNat 64 (8 + d))) (by
    brun [hc.good.x0, hdr_enc (show Crt.sNib < 32 by decide), hc.st (i := Crt.sNib) (by decide), h3,
      ofNat_add_ofNat]
    rw [Nat.add_comm]) rfl rfl rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain o₁ := writeW_outside s.mem P (d := 8 * Crt.sNib) (BitVec.ofNat 64 (8 + d)) (by decide)
  rw [← hm₁] at o₁
  obtain f₁ : Frm P (crtWinRanges wx) s.mem s₁.mem := Frm.of_outside o₁ (by simp [crtWinRanges])
  obtain hc₁ := hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide))
  obtain hh₁ : ∀ k < 32, k ≠ Crt.sNib → word s₁.mem P (8 * k) = word s.mem P (8 * k) := fun k hk h => by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h)]
  refine WP.seq (WP.mono (PublicPower.select_ok hc₁ hw hw' hv16
    (by rw [hh₁ _ (by decide) (by decide)]; exact ht) (by rw [hm₁, word_writeW_self]))
    fun s₂ ⟨hc₂, hT₂, o₂, k₂⟩ => ?_)
  obtain f₂ : Frm P (crtWinRanges wx) s₁.mem s₂.mem :=
    Frm.of_outside (o₂.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (by omega_arith) (by omega_arith))
      (by simp [crtWinRanges])
  obtain hh₂ : ∀ k < 32, word s₂.mem P (8 * k) = word s₁.mem P (8 * k) := fun k hk =>
    o₂.word (Or.inl (hdr_lt_slot wx Crt.aT hk)) (by omega_arith)
  refine WP.seq (WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc₂.good (Nat.le_refl _)
    hw (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc₂.inv (by rw [hc₂.n, hc₂.x]; exact hA)) fun s₃ ⟨_, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [hc₂.n] at hlt₃ hm₃
  obtain f₃ : Frm P (crtWinRanges wx) s₂.mem s₃.mem := Frm.of_arrays ha₃ (by simp [crtWinRanges])
  obtain hc₃ := hc₂.of_win f₃ k₃.wr (k₃.gpr .x0 (by decide))
  obtain tab₃ : word s₃.mem P (8 * Crt.sTab) = off P (slot wx 8) := by
    rw [ha₃.hslot (by decide), hh₂ _ (by decide), hh₁ _ (by decide) (by decide)]
    exact ht
  obtain nib₃ : word s₃.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (8 + d) := by
    rw [ha₃.hslot (by decide), hh₂ _ (by decide), hm₁, word_writeW_self]
  refine WP.mono (put_ok hc₃ hw hw' hv16 tab₃ nib₃) fun t ⟨hct, hE, o₄, k₄⟩ => ?_
  obtain f03 : Frm P (crtWinRanges wx) s.mem s₃.mem := (f₁.trans f₂).trans f₃
  refine ⟨hct, by rw [hE]; exact hlt₃, ?_, fun j hj hjv => ?_, fun j hj h1 h2 h3 h4 => ?_,
    fun k hk h1 _ _ => ?_, (win_work f03).trans (ent_work o₄ hv16),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · rw [hE, hm₃, hT₂, hc₂.x, win_ent f₁ hn hv16]
  · rw [ent_ent o₄ hn hj hjv, win_ent f03 hn hj]
  · rw [ent_arr o₄ hn hj, win_arr f03 hn hj h1 h2 h3 h4]
  · rw [ent_hdr o₄ hk, ha₃.hslot hk, hh₂ k hk, hh₁ k hk h1]

/-- The public digit `Q mod 8`: its bucket becomes its product with `[aXc]`
unless it is zero, when nothing changes. -/
theorem publicHalf_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc Q : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hQ : word s.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 Q) (hQ' : Q < 2 ^ 64) (hA : Xc < N) :
    WP isa (seqs [.block publicDigit, .ite (.zero .x .x3) (.block []) (publicBucket M.mm)]) s fun t =>
      CExpCtx t P wx minv N Xc ∧
      (Q % 8 ≠ 0 → wv t.mem P (slot wx (8 + (8 + Q % 8))) wx < N ∧
        wv t.mem P (slot wx (8 + (8 + Q % 8))) wx * 2 ^ (64 * wx) % N =
          wv s.mem P (slot wx (8 + (8 + Q % 8))) wx * Xc % N) ∧
      (∀ j < 16, j ≠ 8 + Q % 8 ∨ Q % 8 = 0 →
        wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx) ∧
      (∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT →
        wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain hd8 : Q % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (publicDigit_ok hc hQ hQ') fun u ⟨⟨h3, hm⟩, hk⟩ => ?_)
  obtain hf : Frm P (crtWinRanges wx) s.mem u.mem := hm ▸ Frm.refl _ _ _
  obtain hu := hc.of_win hf hk.wr (hk.gpr .x0 (by decide))
  obtain hz := PublicPower.eval_zero_x3 h3 (show Q % 8 < 2 ^ 64 by omega_arith)
  by_cases hzero : Q % 8 = 0
  · refine WP.ite true (by rw [hz, hzero]; rfl) (fun _ => WP.block_nil ?_) (by simp)
    exact ⟨hu, fun h => absurd hzero h, fun _ _ _ => by rw [hm], fun _ _ _ _ _ _ => by rw [hm],
      fun _ _ _ _ _ => by rw [hm], win_work hf, hk.mono (by decide)⟩
  · refine WP.ite false (by rw [hz]; simp [hzero]) (by simp) (fun _ => ?_)
    refine WP.mono (publicBucket_ok M hu hw hw' hd8 (hm ▸ ht) h3 hA)
      fun t ⟨hct, hlt, hval, hoth, harr, hhdr, hfrm, hkt⟩ => ?_
    rw [hm] at hval hoth harr hhdr hfrm
    exact ⟨hct, fun _ => ⟨hlt, hval⟩, fun j hj h => hoth j hj (h.resolve_right hzero), harr, hhdr,
      hfrm, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! ### `Dsa.SharedPower`, which this module and modules that import it used -/

section

/-!
# Two powers of one base with shared squarings: the arithmetic

Right to left, three bits of the exponent at a time: at digit `i` the base's
power `A = g^(8^i)` is multiplied into the bucket of the digit's value, so
bucket `d` holds `g^(bexp e k d)` after `k` digits, and the product of
`bucket_d^d` over the digits' values is `g^(e mod 8^k)`.

That product is taken by a running product from the last bucket down: `cy`
is the exponent of the product of the buckets so far, and `cx` of the
product of those products.
-/

@[expose] public section

namespace VG.Proof.Dsa.Shared

/-- The exponent of bucket `d` after `k` digits of `e`: the sum of `8^i`
over the digits `i < k` of `e` that are `d`. -/
def bexp (e : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, d => bexp e k d + if e / 8 ^ k % 8 = d then 8 ^ k else 0

theorem bexp_zero (e d : Nat) : bexp e 0 d = 0 := rfl

theorem bexp_succ (e k d : Nat) :
    bexp e (k + 1) d = bexp e k d + if e / 8 ^ k % 8 = d then 8 ^ k else 0 := rfl

/-- The digit's own bucket takes `8^k`. -/
theorem bexp_digit (e k : Nat) : bexp e (k + 1) (e / 8 ^ k % 8) = bexp e k (e / 8 ^ k % 8) + 8 ^ k := by
  rw [bexp_succ, ite_eq_left rfl]

/-- Every other bucket is as it was. -/
theorem bexp_other {e k d : Nat} (h : e / 8 ^ k % 8 ≠ d) : bexp e (k + 1) d = bexp e k d := by
  rw [bexp_succ, ite_eq_right h, Nat.add_zero]

/-- The buckets' weighted sum is the exponent's low digits. -/
theorem bexp_sum (e k : Nat) :
    bexp e k 1 + 2 * bexp e k 2 + 3 * bexp e k 3 + 4 * bexp e k 4 + 5 * bexp e k 5 + 6 * bexp e k 6 +
      7 * bexp e k 7 = e % 8 ^ k := by
  induction k with
  | zero => simp only [bexp_zero, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    have hd : e / 8 ^ k % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_pow_succ, ← ih]
    simp only [bexp_succ]
    generalize e / 8 ^ k % 8 = d at hd
    generalize (8 : Nat) ^ k = p
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [reduceCtorEq, Nat.reduceEqDiff, ↓reduceIte] <;> omega

/-- Once the exponent's digits are exhausted, the weighted sum is the exponent. -/
theorem bexp_sum_all {e k : Nat} (h : e / 8 ^ k = 0) :
    bexp e k 1 + 2 * bexp e k 2 + 3 * bexp e k 3 + 4 * bexp e k 4 + 5 * bexp e k 5 + 6 * bexp e k 6 +
      7 * bexp e k 7 = e := by
  rw [bexp_sum, Nat.mod_eq_of_lt]
  exact (Nat.div_eq_zero_iff_lt (Nat.pow_pos (by decide))).mp h

/-- The exponent of the product of the buckets from 7 down to `7 - n`. -/
def cy (b : Nat → Nat) : Nat → Nat
  | 0 => b 7
  | n + 1 => cy b n + b (6 - n)

/-- The exponent of the product of those products. -/
def cx (b : Nat → Nat) : Nat → Nat
  | 0 => b 7
  | n + 1 => cx b n + cy b (n + 1)

theorem cx_six (b : Nat → Nat) :
    cx b 6 = b 1 + 2 * b 2 + 3 * b 3 + 4 * b 4 + 5 * b 5 + 6 * b 6 + 7 * b 7 := by
  simp only [cx, cy, Nat.reduceSub]
  omega

/-- A digit of a value whose low bytes are `v`: `v`'s, while the digit lies
within them. -/
theorem digit_low {a v n i : Nat} (hi : 3 * i + 3 ≤ 8 * n) :
    (256 ^ n * a + v) / 8 ^ i % 8 = v / 8 ^ i % 8 := by
  have h256 : (256 : Nat) ^ n = 8 ^ (i + 1) * 2 ^ (8 * n - 3 * (i + 1)) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul, ← Nat.pow_mul,
      ← Nat.pow_add]
    congr 1
    omega
  rw [h256, Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_add_div (Nat.pow_pos (by decide)),
    Nat.mul_add_mod]

/-! ## The exponent's bytes, three at a time from the end -/

open VG.Proof.Bignum (pre pre_succ pre_zero)

/-- The digits in the group of bytes below index `r`: eight for three
bytes, and six or three for the last two bytes or one. -/
def gcount (r : Nat) : Nat := if 3 ≤ r then 8 else if 2 ≤ r then 6 else 3

/-- The value of the up to three bytes below index `r`. -/
def gval (bs : List Byte) (r : Nat) : Nat :=
  (bs[r - 1]?.getD 0).toNat + (if 2 ≤ r then 256 * (bs[r - 2]?.getD 0).toNat else 0) +
    (if 3 ≤ r then 65536 * (bs[r - 3]?.getD 0).toNat else 0)

theorem gcount_pos (r : Nat) : 1 ≤ gcount r := by
  unfold gcount; split
  · decide
  · split <;> decide

theorem gcount_le (r : Nat) : gcount r ≤ 8 := by
  unfold gcount; split
  · decide
  · split <;> decide

theorem gval_lt (bs : List Byte) (r : Nat) : gval bs r < 2 ^ 24 := by
  unfold gval
  have h1 := (bs[r - 1]?.getD 0).isLt
  have h2 := (bs[r - 2]?.getD 0).isLt
  have h3 := (bs[r - 3]?.getD 0).isLt
  split <;> split <;> omega

theorem getD_getElem (bs : List Byte) {i : Nat} (hi : i < bs.length) : bs[i]?.getD 0 = bs[i] := by
  rw [List.getElem?_eq_getElem hi]; rfl

/-- The group's value and count as the code computes them: one byte left, -/
theorem gval_one (bs : List Byte) {r : Nat} (hr : r = 1) (hl : r ≤ bs.length) :
    gval bs r = (bs[r - 1]'(by omega)).toNat ∧ gcount r = 3 := by
  subst hr
  simp only [gval, gcount, Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero,
    getD_getElem bs (show 0 < bs.length by omega), and_self]

/-- two, -/
theorem gval_two (bs : List Byte) {r : Nat} (hr : r = 2) (hl : r ≤ bs.length) :
    gval bs r = (bs[r - 1]'(by omega)).toNat + 2 ^ 8 * (bs[r - 1 - 1]'(by omega)).toNat ∧ gcount r = 6 := by
  subst hr
  simp only [gval, gcount, Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero, Nat.le_refl,
    getD_getElem bs (show 0 < bs.length by omega), getD_getElem bs (show 1 < bs.length by omega),
    Nat.reducePow, and_self]

/-- or three and more. -/
theorem gval_three (bs : List Byte) {r : Nat} (hr : 3 ≤ r) (hl : r ≤ bs.length) :
    gval bs r = (bs[r - 1]'(by omega)).toNat + 2 ^ 8 * (bs[r - 1 - 1]'(by omega)).toNat +
      2 ^ 16 * (bs[r - 1 - 1 - 1]'(by omega)).toNat ∧ gcount r = 8 := by
  have e2 : r - 1 - 1 = r - 2 := by omega
  have e3 : r - 2 - 1 = r - 3 := by omega
  simp only [gval, gcount, hr, show 2 ≤ r by omega, ↓reduceIte, getD_getElem bs (show r - 1 < bs.length by omega),
    getD_getElem bs (show r - 2 < bs.length by omega), getD_getElem bs (show r - 3 < bs.length by omega),
    Nat.reducePow, e2, e3, and_self]

/-- The bytes below `r` are those below `r - 3`, and the group's. -/
theorem pre_group (bs : List Byte) {r : Nat} (hr : 1 ≤ r) (hrl : r ≤ bs.length) :
    pre bs r = 256 ^ min 3 r * pre bs (r - 3) + gval bs r ∧ gval bs r < 256 ^ min 3 r := by
  have g (i : Nat) (hi : i < bs.length) : (bs[i]?.getD 0) = bs[i] := by
    rw [List.getElem?_eq_getElem hi]; rfl
  unfold gval
  rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | h3
  · have h1 : pre bs 1 = (bs[0]'(by omega)).toNat := by
      simpa only [Nat.zero_add, Nat.mul_zero, pre_zero] using pre_succ bs (i := 0) (by omega)
    have b1 := (bs[0]'(by omega)).isLt
    simp only [Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero, pre_zero, Nat.mul_zero, Nat.zero_add,
      g 0 (by omega), show min 3 1 = 1 by decide, Nat.pow_one]
    omega
  · have h1 : pre bs 1 = (bs[0]'(by omega)).toNat := by
      simpa only [Nat.zero_add, Nat.mul_zero, pre_zero] using pre_succ bs (i := 0) (by omega)
    have h2 : pre bs 2 = 256 * pre bs 1 + (bs[1]'(by omega)).toNat := pre_succ bs (i := 1) (by omega)
    have b1 := (bs[0]'(by omega)).isLt
    have b2 := (bs[1]'(by omega)).isLt
    simp only [Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero, pre_zero, Nat.mul_zero, Nat.zero_add,
      g 0 (by omega), g 1 (by omega), show min 3 2 = 2 by decide, Nat.le_refl]
    omega
  · have h1 := pre_succ bs (i := r - 3) (by omega)
    have h2 := pre_succ bs (i := r - 2) (by omega)
    have h3' := pre_succ bs (i := r - 1) (by omega)
    have b1 := (bs[r - 3]'(by omega)).isLt
    have b2 := (bs[r - 2]'(by omega)).isLt
    have b3 := (bs[r - 1]'(by omega)).isLt
    rw [show r - 3 + 1 = r - 2 by omega] at h1
    rw [show r - 2 + 1 = r - 1 by omega] at h2
    rw [show r - 1 + 1 = r by omega] at h3'
    simp only [h3, show 2 ≤ r by omega, ↓reduceIte, g (r - 1) (by omega), g (r - 2) (by omega),
      g (r - 3) (by omega), Nat.min_eq_left h3]
    omega

/-- The group's digits are the exponent's next ones. -/
theorem group_digit (bs : List Byte) {r i : Nat} (hr : 1 ≤ r) (hrl : r ≤ bs.length) (hi : i < gcount r) :
    pre bs r / 8 ^ i % 8 = gval bs r / 8 ^ i % 8 := by
  obtain ⟨h, -⟩ := pre_group bs hr hrl
  rw [h]
  by_cases h3 : 3 ≤ r
  · rw [Nat.min_eq_left h3]
    exact digit_low (by unfold gcount at hi; simp only [h3, ↓reduceIte] at hi; omega)
  · rw [show r - 3 = 0 by omega, pre_zero, Nat.mul_zero, Nat.zero_add]

/-- After the group's digits, the bytes below `r - 3` are left. -/
theorem group_rest (bs : List Byte) {r : Nat} (hr : 1 ≤ r) (hrl : r ≤ bs.length) :
    pre bs r / 8 ^ gcount r = pre bs (r - 3) := by
  obtain ⟨h, hlt⟩ := pre_group bs hr hrl
  rw [h]
  unfold gcount
  rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | h3
  · simp only [Nat.reduceLeDiff, ↓reduceIte, Nat.reduceSub, pre_zero, Nat.mul_zero, Nat.zero_add] at hlt ⊢
    exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide))
  · simp only [Nat.reduceLeDiff, ↓reduceIte, Nat.reduceSub, pre_zero, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
      at hlt ⊢
    exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide))
  · rw [Nat.min_eq_left h3] at hlt ⊢
    simp only [h3, ↓reduceIte]
    rw [show (256 : Nat) ^ 3 = 8 ^ 8 by decide] at hlt ⊢
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hlt, Nat.add_zero]

end VG.Proof.Dsa.Shared

end

end

/-! # One digit of both exponents

After `k` digits, bucket `d` of `x` holds `g^(bexp x k d)`, bucket `d` of
`q` holds `g^(bexp q k d)`, and `[aXc]` holds `g^(8^k)`, all in Montgomery
form. A digit multiplies `[aXc]` into the bucket of each exponent's digit
(`q`'s only when it is not zero), and cubes `[aXc]` by three squarings. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- The buckets and the base's power after `k` digits of `ex` and `eq`. -/
structure DigitInv (P : Addr) (wx : Nat) (minv : BitVec 64) (N g ex eq k : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv N (wv t.mem P (slot wx Crt.aXc) wx)
  tab : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)
  lt : ∀ j < 16, wv t.mem P (slot wx (8 + j)) wx < N
  xs : ∀ d < 8, wv t.mem P (slot wx (8 + d)) wx % N = g ^ bexp ex k d * 2 ^ (64 * wx) % N
  qs : ∀ d < 8, d ≠ 0 → wv t.mem P (slot wx (8 + (8 + d))) wx % N = g ^ bexp eq k d * 2 ^ (64 * wx) % N
  alt : wv t.mem P (slot wx Crt.aXc) wx < N
  a : wv t.mem P (slot wx Crt.aXc) wx % N = g ^ 8 ^ k * 2 ^ (64 * wx) % N

/-- `[aXc] := [aXc]² R⁻¹`. -/
theorem baseSq_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hA : Xc < N) :
    WP isa (M.mm Crt.aXc Crt.aXc Crt.aXc) s fun t =>
      CExpCtx t P wx minv N (wv t.mem P (slot wx Crt.aXc) wx) ∧ wv t.mem P (slot wx Crt.aXc) wx < N ∧
      wv t.mem P (slot wx Crt.aXc) wx * 2 ^ (64 * wx) % N = Xc * Xc % N ∧
      Arrays P wx [aAcc, aTmp, Crt.aXc] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  obtain hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  refine WP.mono (M.mm_ok (o := Crt.aXc) (a := Crt.aXc) (b := Crt.aXc) hc.good (Nat.le_refl _) hw
    (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc.inv (by rw [hc.n, hc.x]; exact hA)) fun t ⟨hg, hlt, hm, ha, k⟩ => ?_
  rw [hc.n] at hlt hm
  rw [hc.x] at hm
  refine ⟨⟨hg, hc.scrT.congr k.wr, (ha.wv_of_not_mem (show aN < 8 by decide) (by decide) hnZ).trans hc.n, ?_,
    rfl⟩, hlt, hm, ha, k⟩
  rw [ha.word0_of_not_mem (show aN < 8 by decide) (by decide) hnZ (by omega_arith)]
  exact hc.inv

/-- The digits' values and count move on. -/
theorem digitEnd_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc V Q b : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hV : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64)
    (hQ : word s.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 Q) (hQ' : Q < 2 ^ 64)
    (hb : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) :
    WP isa (.block digitEnd) s fun t =>
      (t.mem = ((s.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (V / 8))).writeW
        (off P (8 * Crt.sMaskX)) (BitVec.ofNat 64 (Q / 8))).writeW (off P (8 * Crt.sBit))
          (BitVec.ofNat 64 (b - 1)) ∧ t.gpr .x3 = BitVec.ofNat 64 (b - 1)) ∧ Keep [.x3] s t := by
  obtain hQ₁ : (s.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (V / 8))).readW (off P (8 * Crt.sMaskX)) 64 =
      BitVec.ofNat 64 Q := by
    rw [← hQ]; exact hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) (by decide) (by decide)
  obtain hb₂ : (((s.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (V / 8))).writeW
      (off P (8 * Crt.sMaskX)) (BitVec.ofNat 64 (Q / 8))).readW (off P (8 * Crt.sBit)) 64) =
      BitVec.ofNat 64 b := by
    rw [← hb]
    exact (hdrStore_hdr (i := Crt.sMaskX) _ _ _ (by decide) (by decide) (by decide)).trans
      (hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) (by decide) (by decide))
  refine WP.keep [.x3] ?_ rfl rfl rfl
  brun [digitEnd, hc.good.x0, hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show Crt.sMaskX < 32 by decide),
    hdr_enc (show Crt.sBit < 32 by decide), hc.ld (i := Crt.sV) (by decide), hc.st (i := Crt.sV) (by decide),
    hc.ld (i := Crt.sMaskX) (by decide), hc.st (i := Crt.sMaskX) (by decide),
    hc.ld (i := Crt.sBit) (by decide), hc.st (i := Crt.sBit) (by decide), hV, hQ₁, hb₂,
    WindowVector.shr3_width hV', WindowVector.shr3_width hQ', VG.Offset.ofNat_sub_ofNat hb1]

theorem digit_eq (mul : Nat → Nat → Nat → Prog isa) : digit mul =
    seqs (([.block secretDigit, Crt.select, mul Crt.aT Crt.aT Crt.aXc, store] : List (Prog isa)) ++
      (([.block publicDigit, .ite (.zero .x .x3) (.block []) (publicBucket mul)] : List (Prog isa)) ++
        ([mul Crt.aXc Crt.aXc Crt.aXc, mul Crt.aXc Crt.aXc Crt.aXc, mul Crt.aXc Crt.aXc Crt.aXc,
          .block digitEnd] : List (Prog isa)))) := rfl

/-- One digit of each exponent, the low three bits of the values `V` and
`Q` in `sV` and `sMaskX`: the buckets and the base's power move from `k`
digits to `k + 1`, the values move down three bits, and the digits' count
`b` drops, into `x3`. -/
theorem digit_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N g ex eq k V Q b : Nat}
    (hw : 8 ≤ wx) (hw' : wx < 2 ^ 30) (hd : wx % 8 = 0) (hR : Nat.Coprime (2 ^ (64 * wx)) N)
    (hI : DigitInv P wx minv N g ex eq k s)
    (hV : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64) (hVd : V % 8 = ex / 8 ^ k % 8)
    (hQ : word s.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 Q) (hQ' : Q < 2 ^ 64) (hQd : Q % 8 = eq / 8 ^ k % 8)
    (hb : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) :
    WP isa (digit M.mm) s fun t => DigitInv P wx minv N g ex eq (k + 1) t ∧
      word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (V / 8) ∧
      word t.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 (Q / 8) ∧
      word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧ t.gpr .x3 = BitVec.ofNat 64 (b - 1) ∧
      (∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT → j ≠ Crt.aXc →
        wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ i < 32, i ≠ Crt.sNib → i ≠ Crt.sEnt → i ≠ Crt.sJ → i ≠ Crt.sV → i ≠ Crt.sMaskX → i ≠ Crt.sBit →
        word t.mem P (8 * i) = word s.mem P (8 * i)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hI.ctx.scrT.nowrap
  obtain hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  obtain hw2 : 2 ≤ wx := by omega_arith
  obtain hdx : ex / 8 ^ k % 8 < 8 := Nat.mod_lt _ (by decide)
  obtain hdq : eq / 8 ^ k % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [digit_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (secretBucket_ok M hI.ctx hw hw' hd hI.tab hV hV' hI.alt)
    fun a ⟨hca, ltA, valA, othA, arrA, hdrA, frmA, kA⟩ => ?_)
  rw [hVd] at ltA valA othA
  refine wp_seqs_append (by simp) (by simp) (WP.mono (publicHalf_ok M hca hw2 hw'
    ((hdrA _ (by decide) (by decide) (by decide) (by decide)).trans hI.tab)
    ((hdrA _ (by decide) (by decide) (by decide) (by decide)).trans hQ) hQ' hI.alt)
    fun b' ⟨hcb, valB, othB, arrB, hdrB, frmB, kB⟩ => ?_)
  rw [hQd] at valB othB
  simp only [seqs]
  refine WP.seq (WP.mono (baseSq_ok M hcb hw2 hw' hI.alt) fun c₁ ⟨hc₁, lt₁, v₁, a₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (baseSq_ok M hc₁ hw2 hw' lt₁) fun c₂ ⟨hc₂, lt₂, v₂, a₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (baseSq_ok M hc₂ hw2 hw' lt₂) fun c₃ ⟨hc₃, lt₃, v₃, a₃, k₃⟩ => ?_)
  obtain a13 : Arrays P wx [aAcc, aTmp, Crt.aXc] b'.mem c₃.mem := (a₁.trans a₂).trans a₃
  obtain hdrC : ∀ i < 32, i ≠ Crt.sNib → i ≠ Crt.sEnt → i ≠ Crt.sJ →
      word c₃.mem P (8 * i) = word s.mem P (8 * i) := fun i hi h1 h2 h3 => by
    rw [a13.hslot hi, hdrB i hi h1 h2 h3, hdrA i hi h1 h2 h3]
  refine WP.mono (digitEnd_ok hc₃ (V := V) (Q := Q) (b := b)
    ((hdrC _ (by decide) (by decide) (by decide) (by decide)).trans hV) hV'
    ((hdrC _ (by decide) (by decide) (by decide) (by decide)).trans hQ) hQ'
    ((hdrC _ (by decide) (by decide) (by decide) (by decide)).trans hb) hb1) fun t ⟨⟨hm, h3⟩, kD⟩ => ?_
  obtain oD : Outside P 136 120 c₃.mem t.mem := by
    rw [hm]
    exact ((fn_outside _ P _ (by decide) (by decide)).trans (fn_outside _ P _ (by decide) (by decide))).trans
      (fn_outside _ P _ (by decide) (by decide))
  -- The entries, in terms of the state after the buckets' updates.
  obtain ent : ∀ j < 16, wv t.mem P (slot wx (8 + j)) wx = wv b'.mem P (slot wx (8 + j)) wx := fun j hj => by
    rw [fn_ent oD hn hj, arr_ent a13 (by decide) hn hj]
  obtain entX : ∀ d < 8, wv b'.mem P (slot wx (8 + d)) wx = wv a.mem P (slot wx (8 + d)) wx := fun d hd' =>
    othB d (by omega_arith) (Or.inl (by omega_arith))
  obtain aX : wv t.mem P (slot wx Crt.aXc) wx = wv c₃.mem P (slot wx Crt.aXc) wx := fn_arr oD hn (by decide)
  obtain aval : wv c₃.mem P (slot wx Crt.aXc) wx % N = g ^ 8 ^ (k + 1) * 2 ^ (64 * wx) % N := by
    obtain e₁ := VG.Proof.Bignum.mont_sq hR hI.a v₁
    obtain e₂ := VG.Proof.Bignum.mont_sq hR e₁ v₂
    obtain e₃ := VG.Proof.Bignum.mont_sq hR e₂ v₃
    rw [e₃, show 2 * (2 * (2 * 8 ^ k)) = 8 ^ (k + 1) by rw [Nat.pow_succ]; omega_arith]
  obtain xval : ∀ d < 8, wv a.mem P (slot wx (8 + d)) wx % N = g ^ bexp ex (k + 1) d * 2 ^ (64 * wx) % N := by
    intro d hd'
    by_cases he : ex / 8 ^ k % 8 = d
    · subst he
      rw [bexp_digit]
      exact mont_mulT hR (hI.xs _ hd') hI.a valA
    · rw [othA d (by omega_arith) (Ne.symm he), bexp_other he]
      exact hI.xs d hd'
  obtain qval : ∀ d < 8, d ≠ 0 →
      wv b'.mem P (slot wx (8 + (8 + d))) wx % N = g ^ bexp eq (k + 1) d * 2 ^ (64 * wx) % N := by
    intro d hd' hd0
    by_cases he : eq / 8 ^ k % 8 = d
    · subst he
      obtain hv := (valB hd0).2
      rw [othA _ (by omega_arith) (by omega_arith)] at hv
      rw [bexp_digit]
      exact mont_mulT hR (hI.qs _ hd' hd0) hI.a hv
    · rw [othB (8 + d) (by omega_arith) (Or.inl (by omega_arith)), othA _ (by omega_arith) (by omega_arith),
        bexp_other he]
      exact hI.qs d hd' hd0
  obtain ltB : ∀ j < 16, wv b'.mem P (slot wx (8 + j)) wx < N := by
    intro j hj
    by_cases hq : j = 8 + eq / 8 ^ k % 8 ∧ eq / 8 ^ k % 8 ≠ 0
    · rw [hq.1]; exact (valB hq.2).1
    · rw [othB j hj (by omega_arith)]
      by_cases hx : j = ex / 8 ^ k % 8
      · rw [hx]; exact ltA
      · rw [othA j hj hx]; exact hI.lt j hj
  refine ⟨⟨by rw [aX]; exact ctx_of_fn hc₃ oD kD.wr (kD.gpr .x0 (by decide)), ?_, fun j hj => ?_, fun d hd' => ?_,
    fun d hd' hd0 => ?_, by rw [aX]; exact lt₃, by rw [aX]; exact aval⟩, ?_, ?_, ?_, h3, fun j hj h1 h2 h3 h4 h5 => ?_,
    fun i hi h1 h2 h3 h4 h5 h6 => ?_, ?_, ((((kA.trans kB).trans k₁).trans k₂).trans k₃).trans kD |>.mono (by decide)⟩
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrC _ (by decide) (by decide) (by decide) (by decide)]
    exact hI.tab
  · rw [ent j hj]; exact ltB j hj
  · rw [ent d (by omega_arith), entX d hd']; exact xval d hd'
  · rw [ent (8 + d) (by omega_arith)]; exact qval d hd' hd0
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, word_writeW_self]
  · rw [fn_arr oD hn hj, a13.wv_of_not_mem hj (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h5⟩) hnZ,
      arrB j hj h1 h2 h3 h4, arrA j hj h1 h2 h3 h4]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h6), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h5),
      hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h4), hdrC i hi h1 h2 h3]
  · exact ((frmA.trans frmB).trans (arrays_work a13 (by decide))).trans (fn_work oD)

end VG.Proof.Dsa.AArch64.SharedPower
