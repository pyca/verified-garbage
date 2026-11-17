module

public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorInner
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorScan
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

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
