module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.CheckDomain
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Ffdh.RISCV64.VettedValidation
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.CheckDomain
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_check_domain` on RISC-V, with the standard domains

`code` compares the domain with each standard domain of the table
(`recognize`): every record's comparison (`compare_ok`, `record_ok`) is
accumulated into `a5` without a branch (`acc_ok`), so that `a5 = 0` exactly
when the domain matches none (`scan_ok`). A match is a valid domain
(`VettedValidation.matched_domain_valid`); otherwise the full check runs
(`Domain.cd_verified`, on the state without the table: `fallback_run`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.VettedValidation

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Impl.Ffdh.RISCV64.VettedValidation VG.Impl.Ffdh.VettedGroups

/-! ## The comparisons -/

/-- The domain matches `g`. -/
def Hit (g : Group) (k : Nat) (dom : List Byte) : Prop := g.len = k ∧ dom = g.domain.take dom.length

instance (g : Group) (k : Nat) (dom : List Byte) : Decidable (Hit g k dom) := by unfold Hit; infer_instance

/-- The registers the scan writes. -/
def clobbers : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a5]

/-- The domain's arguments, kept throughout the scan. -/
structure Ctx (src : Addr) (k : Nat) (dom : List Byte) (s : State) : Prop where
  source : s.gpr .a0 = src
  length : s.gpr .a1 = BitVec.ofNat 64 dom.length
  width : s.gpr .a2 = BitVec.ofNat 64 k
  read : InRegions (s.rd ++ s.wr) src dom.length
  bytes : Spec.Rsa.bytesAt s.mem src dom.length = dom
  shape : dom.length = 2 * k ∨ dom.length = 3 * k
  lower : 64 ≤ k
  upper : k ≤ 1024

/-- A record of the table at `ptr`. -/
structure RecordAt (ptr : Addr) (g : Group) (s : State) : Prop where
  len : 0 < g.len
  lenFit : g.len ≤ 1024
  bitsPos : 0 < g.bits
  bitsFit : g.bits < 2048
  read : InRegions (s.rd ++ s.wr) (ptr + BitVec.ofNat 64 8) (3 * g.len)
  bytes : Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 8) (3 * g.len) = g.domain

/-- The records of `gs` from `ptr` on. -/
def TableAt (ptr : Addr) : List Group → State → Prop
  | [], _ => True
  | g :: gs, s => RecordAt ptr g s ∧ TableAt (ptr + BitVec.ofNat 64 (8 + 3 * g.len)) gs s

theorem Ctx.after {src : Addr} {k : Nat} {dom : List Byte} {s t : State} {rs : List Reg}
    (h : Ctx src k dom s) (mem : t.mem = s.mem) (rest : Keep rs s t)
    (hr : ∀ r ∈ ([.a0, .a1, .a2] : List Reg), r ∉ rs := by decide) : Ctx src k dom t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  refine ⟨(rest.gpr hr.1).trans h.source, (rest.gpr hr.2.1).trans h.length, (rest.gpr hr.2.2).trans h.width,
    ?_, ?_, h.shape, h.lower, h.upper⟩
  · rw [rest.2.1, rest.2.2]; exact h.read
  · rw [mem]; exact h.bytes

theorem RecordAt.after {rs : List Reg} {ptr : Addr} {g : Group} {s t : State}
    (h : RecordAt ptr g s) (mem : t.mem = s.mem) (rest : Keep rs s t) : RecordAt ptr g t := by
  refine ⟨h.len, h.lenFit, h.bitsPos, h.bitsFit, ?_, ?_⟩
  · rw [rest.2.1, rest.2.2]; exact h.read
  · rw [mem]; exact h.bytes

theorem TableAt.after {rs : List Reg} {ptr : Addr} {gs : List Group} {s t : State}
    (h : TableAt ptr gs s) (mem : t.mem = s.mem) (rest : Keep rs s t) : TableAt ptr gs t := by
  induction gs generalizing ptr with
  | nil => trivial
  | cons g gs ih => exact ⟨h.1.after mem rest, ih h.2⟩

theorem sub_sub_ofNat {n i : Nat} (hi : i ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 (n - i) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem byte_xor_zero (a b : Byte) :
    BitVec.ofNat 64 a.toNat ^^^ BitVec.ofNat 64 b.toNat = 0 ↔ a = b := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    exact BitVec.eq_of_toNat_eq (by have := a.isLt; have := b.isLt; omega)
  · rintro rfl; rfl

theorem snoc_iff {l₁ l₂ : List Byte} {a b : Byte} (h : l₁.length = l₂.length) :
    l₁ ++ [a] = l₂ ++ [b] ↔ l₁ = l₂ ∧ a = b := by
  constructor
  · intro e
    obtain ⟨e1, e2⟩ := List.append_inj e h
    exact ⟨e1, by simpa using e2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- `compare`: `t4 = 0` exactly when the domain's bytes are those at `T`
(`t0`). -/
theorem compare_ok {src T : Addr} {k : Nat} {dom : List Byte} {s : State} (h : Ctx src k dom s)
    (h0 : s.gpr .t0 = T) (hr : InRegions (s.rd ++ s.wr) T dom.length) :
    WP isa Impl.Ffdh.RISCV64.VettedValidation.compare s fun t => (t.gpr .t4 = 0 ↔ dom = Spec.Rsa.bytesAt s.mem T dom.length) ∧
      t.mem = s.mem ∧ Keep [.t0, .t1, .t2, .t3, .t4] s t := by
  have hn : 0 < dom.length := by rcases h.shape with e | e <;> have := h.lower <;> omega
  have hn' : dom.length < 2 ^ 64 := by rcases h.shape with e | e <;> have := h.upper <;> omega
  unfold Impl.Ffdh.RISCV64.VettedValidation.compare
  refine WP.seq (WP.mono (WP.keep [.t2, .t4] (Q := fun t => t.gpr .t2 = BitVec.ofNat 64 dom.length ∧
    t.gpr .t4 = 0 ∧ t.mem = s.mem) (by brun [h.length, exec_li, BitVec.add_zero]; rfl) (by rfl) (by rfl))
    fun s₁ ⟨⟨c2, c4, m1⟩, k1⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.mem = s.mem ∧ Keep [.t0, .t1, .t2, .t3, .t4] s t ∧ t.gpr .t0 = T + BitVec.ofNat 64 i ∧
      (t.gpr .t4 = 0 ↔ Spec.Rsa.bytesAt s.mem src i = Spec.Rsa.bytesAt s.mem T i)
  refine WP.mono (wp_countdown (body := .block compareByte) (cnt := .t2) hn' hn Inv
    (fun i hi t ⟨tm, tk, t0, t4⟩ tc => ?_)
    ⟨m1, k1.mono (by decide), by rw [k1.gpr (by decide), h0, BitVec.add_zero], by
      rw [c4]; simp [Spec.Rsa.bytesAt]⟩ c2) fun t ⟨tm, tk, _, t4⟩ => ⟨?_, tm, tk⟩
  · have ha := h.read
    have hA : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 i) 1 := by
      rw [tk.2.1, tk.2.2]; exact CallLay.inRegions_sub ha (by omega) hn'
    have hB : InRegions (t.rd ++ t.wr) (T + BitVec.ofNat 64 i) 1 := by
      rw [tk.2.1, tk.2.2]; exact CallLay.inRegions_sub hr (by omega) hn'
    have a0 : t.gpr .a0 = src := (tk.gpr (by decide)).trans h.source
    have a1 : t.gpr .a1 = BitVec.ofNat 64 dom.length := (tk.gpr (by decide)).trans h.length
    refine WP.mono (WP.keep [.t0, .t1, .t2, .t3, .t4] (Q := fun u => u.mem = t.mem ∧
      u.gpr .t0 = t.gpr .t0 + BitVec.ofNat 64 1 ∧ u.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1 ∧
      u.gpr .t4 = t.gpr .t4 ||| (BitVec.ofNat 64 (s.mem (src + BitVec.ofNat 64 i)).toNat ^^^
        BitVec.ofNat 64 (s.mem (T + BitVec.ofNat 64 i)).toNat))
      (by unfold compareByte; brun [a0, a1, tc, t0, sub_sub_ofNat (Nat.le_of_lt hi) hn', BitVec.add_zero, hA, hB,
        read_byte64, tm]) (by rfl) (by rfl)) fun u ⟨⟨um, u0, u2, u4⟩, uk⟩ => ⟨⟨um.trans tm, ?_, ?_, ?_⟩, u2⟩
    · exact (tk.trans uk).mono (by decide)
    · rw [u0, t0, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [u4, show ∀ a b : BitVec 64, (a ||| b = 0 ↔ a = 0 ∧ b = 0) from fun _ _ => BitVec.or_eq_zero_iff, t4,
        byte_xor_zero, Pub.bytesAt_succ, Pub.bytesAt_succ,
        snoc_iff (by simp only [VG.Proof.Bignum.bytesAt_length])]
  · rw [t4, h.bytes]

/-- `record g`: `t4 = 0` exactly when the domain matches `g`, whose record
is at `t5`. -/
theorem record_ok {src : Addr} {k : Nat} {dom : List Byte} {s : State} (h : Ctx src k dom s) (g : Group)
    (hr : RecordAt (s.gpr .t5) g s) :
    WP isa (record g) s fun t => (t.gpr .t4 = 0 ↔ Hit g k dom) ∧ t.mem = s.mem ∧
      Keep [.t0, .t1, .t2, .t3, .t4] s t := by
  have hl := hr.lenFit
  have hk := h.upper
  unfold record
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = BitVec.ofNat 64 k - BitVec.ofNat 64 g.len ∧
    t.mem = s.mem) (by brun [h.width, show g.len ≤ 2048 by omega]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have hz : s₁.gpr .t3 = 0 ↔ k = g.len := by
    rw [a3]; exact Domain.sub_ofNat_zero (by omega) (by omega)
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have e : k = g.len := hz.mp (by simpa using hb)
    refine WP.seq (WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = s.gpr .t5 + BitVec.ofNat 64 8 ∧
      t.mem = s₁.mem) (by brun [k1.gpr (r := .t5) (by decide)]) (by rfl) (by rfl)) fun s₂ ⟨⟨a0, m2⟩, k2⟩ => ?_)
    have hm2 : s₂.mem = s.mem := m2.trans m1
    have c2 := h.after hm2 (k1.trans k2)
    have hn : dom.length ≤ 3 * g.len := by rcases h.shape with e' | e' <;> omega
    have hrd : InRegions (s₂.rd ++ s₂.wr) (s.gpr .t5 + BitVec.ofNat 64 8) dom.length := by
      rw [(k1.trans k2).2.1, (k1.trans k2).2.2]
      have := CallLay.inRegions_sub hr.read (off := 0) (l := dom.length) (by omega) (by omega)
      rwa [BitVec.add_zero] at this
    refine WP.mono (compare_ok c2 a0 hrd) fun t ⟨t4, tm, tk⟩ =>
      ⟨?_, tm.trans hm2, ((k1.trans k2).trans tk).mono (by decide)⟩
    rw [t4, hm2, ← Proof.Ffdh.take_bytesAt _ _ hn, hr.bytes]
    unfold Hit
    simp only [e, true_and]
  · have e : k ≠ g.len := fun e => by simp [hz.mpr e] at hb
    refine WP.mono (WP.keep [.t4] (Q := fun t => t.gpr .t4 = 1 ∧ t.mem = s₁.mem) (by brun [exec_li]; rfl)
      (by rfl) (by rfl)) fun t ⟨⟨t4, tm⟩, tk⟩ => ⟨?_, tm.trans m1, (k1.trans tk).mono (by decide)⟩
    rw [t4]
    exact ⟨fun h => absurd h (by decide), fun hh => absurd hh.1.symm e⟩

theorem bits_mask (b : Bool) {n : Nat} (h0 : 0 < n) (h1 : n < 2048) :
    (bmask b &&& BitVec.ofInt 64 (n : Int) = 0) ↔ b = false := by
  cases b
  · simp [bmask]
  · rw [show bmask true = BitVec.allOnes 64 from rfl, BitVec.allOnes_and, BitVec.ofInt_natCast]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega)] at this
      omega
    · intro h; cases h

/-- `accumulate g` and `advance n`: `a5 |= g.bits` if `t4 = 0`. -/
theorem acc_ok (g : Group) {n : Nat} (hb0 : 0 < g.bits) (hb : g.bits < 2048) (hn : n ≤ 4000) (s : State) :
    WP isa (.block (accumulate g ++ advance n)) s fun t =>
      (t.gpr .a5 = 0 ↔ s.gpr .a5 = 0 ∧ s.gpr .t4 ≠ 0) ∧ t.gpr .t5 = s.gpr .t5 + BitVec.ofNat 64 n ∧
        t.mem = s.mem ∧ Keep [.t6, .a5, .t5] s t := by
  refine WP.mono (WP.keep [.t6, .a5, .t5] (Q := fun t => t.gpr .a5 = s.gpr .a5 |||
      ((if BitVec.ofNat 64 0 < s.gpr .t4 then (1 : BitVec 64) else 0) - BitVec.ofNat 64 1 &&&
        BitVec.ofInt 64 (g.bits : Int)) ∧
      t.gpr .t5 = VG.Proof.Mont.off (s.gpr .t5) (n / 2 + (n - n / 2)) ∧ t.mem = s.mem)
    (by unfold accumulate advance; brun [exec_li, exec_logicImm (show imm12 (g.bits : Int) by unfold imm12; omega),
      show n / 2 < 2048 by omega, show n - n / 2 < 2048 by omega]) (by rfl) (by rfl))
    fun t ⟨⟨t5', t5, tm⟩, tk⟩ => ⟨?_, ?_, tm, tk⟩
  · rw [t5', show ∀ a b : BitVec 64, (a ||| b = 0 ↔ a = 0 ∧ b = 0) from fun _ _ => BitVec.or_eq_zero_iff,
      sltu_mask, bits_mask _ hb0 hb]
    simp
  · rw [t5]
    show s.gpr .t5 + BitVec.ofNat 64 (n / 2 + (n - n / 2)) = _
    congr 2
    omega

/-- The scan: `a5 = 0` at the end exactly when it was and the domain
matches none of `gs`. -/
theorem scan_ok {src : Addr} {k : Nat} {dom : List Byte} :
    ∀ (gs : List Group) (s : State), Ctx src k dom s → TableAt (s.gpr .t5) gs s →
      WP isa (scan gs) s fun t => (t.gpr .a5 = 0 ↔ s.gpr .a5 = 0 ∧ ∀ g ∈ gs, ¬Hit g k dom) ∧ t.mem = s.mem ∧
        Keep clobbers s t
  | [], s, _, _ => WP.block_nil ⟨by simp, rfl, Keep.refl _ _⟩
  | g :: gs, s, h, data => by
    have hr := data.1
    unfold scan
    refine WP.seq (WP.mono (record_ok h g hr) fun s₁ ⟨r4, m1, k1⟩ => ?_)
    refine WP.seq (WP.mono (acc_ok g (n := 8 + 3 * g.len) hr.bitsPos hr.bitsFit (by have := hr.lenFit; omega) s₁)
      fun s₂ ⟨a5, t5, m2, k2⟩ => ?_)
    have hm : s₂.mem = s.mem := m2.trans m1
    have k12 := k1.trans k2
    have tail : TableAt (s₂.gpr .t5) gs s₂ := by
      rw [t5, k1.gpr (by decide)]; exact data.2.after hm k12
    refine WP.mono (scan_ok gs s₂ (h.after hm k12) tail) fun t ⟨ta, tm, tk⟩ =>
      ⟨?_, tm.trans hm, (k12.trans tk).mono (by decide)⟩
    rw [ta, a5, k1.gpr (by decide), ne_eq, r4]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

/-! ## The table -/

theorem tableOfBytes (gs : List Group) (ptr : Addr) (s : State)
    (read : InRegions (s.rd ++ s.wr) ptr (gs.flatMap Group.bytes).length)
    (bytes : Spec.Rsa.bytesAt s.mem ptr (gs.flatMap Group.bytes).length = gs.flatMap Group.bytes)
    (bound : (gs.flatMap Group.bytes).length ≤ 17744)
    (valid : ∀ g ∈ gs, 0 < g.len ∧ g.len ≤ 1024 ∧ 0 < g.bits ∧ g.bits < 2048) :
    TableAt ptr gs s := by
  induction gs generalizing ptr with
  | nil => trivial
  | cons g gs ih =>
    have length := VG.Proof.Ffdh.VettedTableFacts.groupBytes_length g
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, length]
    have domainLength : g.domain.length = 3 * g.len := by
      simp only [Group.domain, List.length_append, VG.Proof.Rsa.i2osp_length]
      omega
    have headerLength : (wordBytes g.len ++ wordBytes g.bits).length = 8 := by
      simp only [wordBytes, List.length_append, List.length_map, List.length_range]
    have domain : (((g :: gs).flatMap Group.bytes).drop 8).take (3 * g.len) = g.domain := by
      rw [List.flatMap_cons, Group.bytes, List.append_assoc, ← headerLength,
        List.drop_left, List.take_left' domainLength]
    have tailBytes : (((g :: gs).flatMap Group.bytes).drop (8 + 3 * g.len)).take
        (gs.flatMap Group.bytes).length = gs.flatMap Group.bytes := by
      rw [List.flatMap_cons, ← length, List.drop_left, List.take_length]
    have part (d n : Nat) (size : d + n ≤ ((g :: gs).flatMap Group.bytes).length) :
        InRegions (s.rd ++ s.wr) (ptr + BitVec.ofNat 64 d) n :=
      CallLay.inRegions_sub read size (by omega)
    have slice (d n : Nat) (size : d + n ≤ ((g :: gs).flatMap Group.bytes).length) :
        Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 d) n =
          (((g :: gs).flatMap Group.bytes).drop d).take n := by
      rw [← VG.Proof.Dsa.bytesAt_slice s.mem ptr size, bytes]
    have v := valid g (by simp)
    refine ⟨⟨v.1, v.2.1, v.2.2.1, v.2.2.2, part 8 (3 * g.len) (by rw [total]; omega),
      (slice 8 (3 * g.len) (by rw [total]; omega)).trans domain⟩, ?_⟩
    exact ih _ (part _ _ (by rw [total]))
      ((slice _ _ (by rw [total])).trans tailBytes)
      (by rw [total] at bound; omega) (fun g hg => valid g (by simp [hg]))

theorem consts_table {s : State} {st : Nat} (hc : ConstsOk tableConsts st s) :
    TableAt (s.syms tableSym) groups s := by
  have held := ConstsOk.held1 (name := tableSym) (ws := tableWords) hc
  have bytes : Spec.Rsa.bytesAt s.mem (s.syms tableSym) tableBytes.length = tableBytes := by
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      rw [VG.Proof.Ffdh.VettedTableFacts.table_held_byte held hj]
      exact (List.getElem_eq_getD (h := hj) 0).symm
  have read : InRegions (s.rd ++ s.wr) (s.syms tableSym) tableBytes.length := by
    have := ConstsOk.rd1 (name := tableSym) (ws := tableWords) hc
    rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at this
    rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]
    exact ⟨_, List.mem_append_left _ this, Region.contains_self _ _⟩
  apply tableOfBytes groups _ s read bytes
    (by change tableBytes.length ≤ 17744; rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length])
  intro g hg
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## The contract, with the table -/

open VG.Proof.Ffdh.RISCV64.Domain (cdContract cd_implies cd_correct cd_verified cdDom cdScr ofNat_toNat')

def contract : Contract isa := Spec.Ffdh.checkDomainContract (RISCV64.abi.withConsts tableConsts)

/-- The state without the table's region. -/
def plain (s : State) : State := stripConsts tableConsts s

theorem pre_plain {s : State} (h : contract.pre s) :
    (Spec.Ffdh.checkDomainContract RISCV64.abi).pre (plain s) ∧ ConstsOk tableConsts 0 s :=
  pre_consts.mp h

theorem cd_pre {s : State} (h : contract.pre s) : cdContract.pre (plain s) := cd_implies.pre _ (pre_plain h).1

/-- The domain's bytes. -/
def domain (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat

theorem context {s : State} (h : contract.pre s) : Ctx (s.gpr .a0) (s.gpr .a2).toNat (domain s) s := by
  obtain ⟨hrd, _, _, _, _, ⟨hk, hk'⟩, hL, _, _⟩ := cd_pre h
  have len : (domain s).length = (s.gpr .a1).toNat := by
    simp only [domain, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine ⟨rfl, by rw [len, ofNat_toNat'], by rw [ofNat_toNat'], ?_, by rw [len]; rfl, by rw [len]; exact hL,
    hk, hk'⟩
  rw [len]
  have mem : (cdDom s) ∈ s.rd := stripConsts_rd_mem (K := tableConsts) (by
    show cdDom (plain s) ∈ (plain s).rd; rw [hrd]; exact List.mem_cons_self)
  exact ⟨_, List.mem_append_left _ mem, Region.contains_self _ _⟩

/-- The domain matches none of the standard ones. -/
def Miss (s : State) : Prop := ∀ g ∈ groups, ¬Hit g (s.gpr .a2).toNat (domain s)

/-- After `recognize`. -/
structure Result (s t : State) : Prop where
  miss : t.gpr .a5 = 0 ↔ Miss s
  mem : t.mem = s.mem
  keep : Keep clobbers s t

theorem recognize_ok {s : State} (h : contract.pre s) : WP isa recognize s (Result s) := by
  have input := context h
  have table := consts_table (pre_plain h).2
  unfold recognize
  refine WP.seq (WP.mono (WP.keep [.t5, .a5] (Q := fun t => t.gpr .t5 = s.syms tableSym ∧ t.gpr .a5 = 0 ∧
    t.mem = s.mem) (by brun [exec_lla, exec_li]; rfl) (by rfl) (by rfl)) fun u ⟨⟨u5, ua, m⟩, k⟩ => ?_)
  refine WP.mono (scan_ok groups u (input.after m k) (by rw [u5]; exact table.after m k)) fun t ⟨ta, tm, tk⟩ =>
    ⟨by rw [ta, ua]; simp [Miss], tm.trans m, (k.trans tk).mono (by decide)⟩

theorem cd_pre_congr {s t : State} (h : cdContract.pre s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hr : ∀ r ∈ ([.a0, .a1, .a2, .a3, .a4] : List Reg), t.gpr r = s.gpr r) : cdContract.pre t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨h0, h1, h2, h3, h4⟩ := hr
  simp only [cdContract, cdDom, cdScr] at h ⊢
  rw [hrd, hwr, h0, h1, h2, h3, h4]
  exact h

theorem plain_covers (s : State) : Covers ((plain s).rd ++ (plain s).wr) (s.rd ++ s.wr) :=
  (Covers.of_mem (fun _ h => List.mem_of_mem_take h)).append (Covers.refl _)

/-- The postcondition from its form on the registers. -/
theorem post_of {s t : State} (pre : contract.pre s)
    (h : ((t.gpr .a0).setWidth 32).toNat =
      if Spec.Ffdh.domainValid (s.gpr .a2).toNat (domain s) then 1 else 0) : contract.post s t :=
  post_consts.mpr (post_stripConsts.mp (cd_implies.post (plain s) t (pre_plain pre).1 h))

theorem correct (s : State) (pre : contract.pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ contract.post s t := by
  show WP isa code s fun t => abiPreserved s t ∧ contract.post s t
  unfold code
  refine WP.seq (WP.mono (WP.rdwr (recognize_ok pre)) fun u ⟨res, urd, uwr, usp⟩ => ?_)
  have hpres : ∀ r ∈ preserved, u.gpr r = s.gpr r := fun r hr => res.keep.gpr (by revert r; decide)
  refine WP.ite (u.gpr .a5 != 0) (Steps.eval_nonzero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hit : ¬Miss s := fun m => by simp [res.miss.mpr m] at hb
    have valid : Spec.Ffdh.domainValid (s.gpr .a2).toNat (domain s) = true := by
      obtain ⟨g, hg, hh⟩ : ∃ g ∈ groups, Hit g (s.gpr .a2).toNat (domain s) :=
        Classical.byContradiction fun hc => hit fun g hg hh => hc ⟨g, hg, hh⟩
      exact VG.Proof.Ffdh.VettedValidation.matched_domain_valid hg (context pre).shape ⟨hh.1.symm, hh.2⟩
    refine WP.mono (WP.rdwr (WP.keep [.a0] (Q := fun t => t.gpr .a0 = 1) (by brun [exec_li]; rfl) (by rfl)
      (by rfl))) fun t ⟨⟨t0, kt⟩, _, _, tsp⟩ => ⟨⟨fun r hr => (kt.gpr (by revert r; decide)).trans (hpres r hr),
        tsp.trans usp, (kt.gpr (by decide)).trans (res.keep.gpr (by decide))⟩, post_of pre ?_⟩
    rw [t0, valid]; rfl
  · have cpre : cdContract.pre (plain u) := cd_pre_congr (cd_pre pre)
      (by simp only [plain, stripConsts, State.withRegions_rd, urd]) (by simp only [plain, stripConsts,
        State.withRegions_wr, uwr]) (fun r hr => by
          simp only [plain, stripConsts_gpr]; exact res.keep.gpr (by revert r hr; decide))
    obtain ⟨tr, t, run, ⟨tp, tsp, tra⟩, tpost⟩ := cd_correct (plain u) cpre
    have wide := VG.RISCV64.Exec.widen run (rd := u.rd) (wr := u.wr) (plain_covers u) (Covers.refl _)
    simp only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] at wide
    refine ⟨tr, t.withRegions u.rd u.wr, wide, ⟨fun r hr => ?_, ?_, ?_⟩, post_of pre ?_⟩
    · rw [State.withRegions_gpr, tp r hr]; exact hpres r hr
    · rw [State.withRegions_sp, tsp]; exact usp
    · rw [State.withRegions_gpr, tra]; exact res.keep.gpr (by decide)
    · rw [State.withRegions_gpr]
      have e := tpost
      simp only [cdContract, plain, stripConsts_gpr, stripConsts_mem] at e
      rw [e]
      simp only [domain, res.keep.gpr (r := .a0) (by decide), res.keep.gpr (r := .a1) (by decide),
        res.keep.gpr (r := .a2) (by decide), res.mem]
      exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

/-! ## Constant time -/

/-- The state without the table's region, for the full check. -/
theorem fallback_ct :
    RelCT isa (fun s t => cdContract.pre (plain s) ∧ cdContract.pre (plain t) ∧ cdContract.pub (plain s) (plain t))
      Impl.Ffdh.RISCV64.Domain.checkDomain (fun _ _ => True) := by
  intro s t ts tt u w ⟨hs, ht, hp⟩ es et
  obtain ⟨ts', u', eu, _⟩ := cd_correct (plain s) hs
  obtain ⟨tt', w', ew, _⟩ := cd_correct (plain t) ht
  have eus := VG.RISCV64.Exec.widen eu (rd := s.rd) (wr := s.wr) (plain_covers s) (Covers.refl _)
  have ewt := VG.RISCV64.Exec.widen ew (rd := t.rd) (wr := t.wr) (plain_covers t) (Covers.refl _)
  simp only [plain, stripConsts, State.withRegions_withRegions, State.withRegions_self] at eus ewt
  rw [(Exec.det es eus).1, (Exec.det et ewt).1]
  exact ⟨Domain.cd_ct _ _ _ _ _ _ hs ht hp eu ew, trivial⟩

/-- The registers of the arguments. -/
def publicRegs : List Reg := [.a0, .a1, .a2, .a3, .a4]

/-- A run with the public data of `a`. -/
structure Start (a s : State) : Prop where
  pre : contract.pre s
  regs : ∀ r ∈ publicRegs, s.gpr r = a.gpr r
  dom : domain s = domain a
  sym : s.syms tableSym = a.syms tableSym
  sp : s.sp = a.sp

theorem start_of_pub {a s : State} (ha : contract.pre a) (hs : contract.pre s) (hp : contract.pub a s) :
    Start a s := by
  have relation := pub_consts.mp
    (show (Spec.Ffdh.checkDomainContract (RISCV64.abi.withConsts [(tableSym, tableWords)])).pub a s from hp)
  have hsym : a.syms tableSym = s.syms tableSym := relation.2 (tableSym, tableWords) List.mem_cons_self
  have base := cd_implies.pub (plain a) (plain s) (pre_plain ha).1 (pre_plain hs).1
    (pub_stripConsts.mpr relation.1)
  obtain ⟨sp, r0, r1, r2, r3, r4, bytes⟩ := base
  refine ⟨hs, ?_, ?_, hsym.symm, sp.symm⟩
  · intro r hr
    simp only [publicRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [r0.symm, r1.symm, r2.symm, r3.symm, r4.symm]
  · exact ((List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp bytes).symm

/-- After `recognize`, from a start. -/
def After (a t : State) : Prop := ∃ s, Start a s ∧ Result s t ∧ t.sp = s.sp

theorem After.miss {a t : State} (h : After a t) : t.gpr .a5 = 0 ↔ Miss a := by
  obtain ⟨s, st, res, _⟩ := h
  rw [res.miss]
  unfold Miss
  rw [st.regs .a2 (by decide), st.dom]

theorem After.cdpre {a t : State} (h : After a t) : cdContract.pre (plain t) := by
  obtain ⟨s, st, res, _⟩ := h
  exact cd_pre_congr (cd_pre st.pre) (by simp only [plain, stripConsts, State.withRegions_rd, res.keep.2.1])
    (by simp only [plain, stripConsts, State.withRegions_wr, res.keep.2.2]) (fun r hr => by
      simp only [plain, stripConsts_gpr]; exact res.keep.gpr (by revert r hr; decide))

theorem After.regs {a t : State} (h : After a t) : ∀ r ∈ publicRegs, t.gpr r = a.gpr r := by
  obtain ⟨s, st, res, _⟩ := h
  intro r hr
  exact (res.keep.gpr (by revert r hr; decide)).trans (st.regs r hr)

theorem After.domain_eq {a t : State} (h : After a t) : domain t = domain a := by
  obtain ⟨s, st, res, _⟩ := h
  unfold domain
  rw [res.mem, res.keep.gpr (r := .a0) (by decide), res.keep.gpr (r := .a1) (by decide)]
  exact st.dom

theorem After.sp' {a t : State} (h : After a t) : t.sp = a.sp := by
  obtain ⟨s, st, _, sp⟩ := h
  exact sp.trans st.sp

theorem After.pub {a s t : State} (hs : After a s) (ht : After a t) : cdContract.pub (plain s) (plain t) := by
  refine ⟨hs.sp'.trans ht.sp'.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hs.regs .a0 (by decide)).trans (ht.regs .a0 (by decide)).symm
  · exact (hs.regs .a1 (by decide)).trans (ht.regs .a1 (by decide)).symm
  · exact (hs.regs .a2 (by decide)).trans (ht.regs .a2 (by decide)).symm
  · exact (hs.regs .a3 (by decide)).trans (ht.regs .a3 (by decide)).symm
  · exact (hs.regs .a4 (by decide)).trans (ht.regs .a4 (by decide)).symm
  · change (domain s).map (·.toNat) = (domain t).map (·.toNat)
    rw [hs.domain_eq, ht.domain_eq]

theorem recognize_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) recognize (fun _ _ => True) := by
  apply RelCT.taint (A := taintSym [tableSym]) (Taint.ofRegs [.a0, .a1, .a2]) _ (by taint_decide)
  intro s t ⟨hs, ht⟩
  refine ⟨⟨hs.sp.trans ht.sp.symm, fun r hr => ?_⟩, fun n hn => ?_⟩
  · simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hs.regs .a0 (by decide)).trans (ht.regs .a0 (by decide)).symm
    · exact (hs.regs .a1 (by decide)).trans (ht.regs .a1 (by decide)).symm
    · exact (hs.regs .a2 (by decide)).trans (ht.regs .a2 (by decide)).symm
  · simp only [List.mem_singleton] at hn
    subst hn
    exact hs.sym.trans ht.sym.symm

theorem anchored_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) code (fun _ _ => True) := by
  have scanWP (s : State) (h : Start a s) : WP isa recognize s (After a) :=
    WP.mono (WP.rdwr (recognize_ok h.pre)) fun t ⟨res, _, _, sp⟩ => ⟨s, h, res, sp⟩
  have scanStage : RelCT isa (fun s t => Start a s ∧ Start a t) recognize
      (fun s t => After a s ∧ After a t) := ((recognize_ct a).wp
        (fun s t h => ⟨scanWP s h.1, scanWP t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have choice : RelCT isa (fun s t => After a s ∧ After a t)
      (.ite (.nonzero .a5) (.block [.li .a0 1]) Impl.Ffdh.RISCV64.Domain.checkDomain) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by
      rw [Steps.eval_nonzero, Steps.eval_nonzero]
      congr 1
      rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, h.1.miss, h.2.miss])
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro s t h
      exact ⟨h.1.1.sp'.trans h.1.2.sp'.symm, by simp [Taint.ofRegs]⟩
    · exact fallback_ct.mono (fun _ _ h => ⟨h.1.1.cdpre, h.1.2.cdpre, After.pub h.1.1 h.1.2⟩) (fun _ _ h => h)
  exact scanStage.seq choice

theorem constantTime : ConstantTime isa contract.pre contract.pub code := by
  intro s t ts tt u w hs ht hp es et
  have left : Start s s := ⟨hs, fun _ _ => rfl, rfl, rfl, rfl⟩
  exact (anchored_ct s s t ts tt u w ⟨left, start_of_pub hs ht hp⟩ es et).1

/-! ## A state meeting the precondition -/

private def satState (words : List (BitVec 64)) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 128 | .a2 => 64 | .a3 => 0x4000 | .a4 => 1056 | _ => 0
  sp := 0x8000
  mem := constMem 0x100000 words
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 17744⟩]
  wr := [⟨0x4000, 8448⟩]
  syms _ := 0x100000

private theorem satPre (words : List (BitVec 64)) :
    (Spec.Ffdh.checkDomainContract RISCV64.abi).pre (stripConsts [(tableSym, words)] (satState words)) := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, RISCV64.abi, RISCV64.argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords]
  repeat' apply And.intro
  all_goals first | rfl | decide | (apply Region.disjoint_of_sep; decide)

private theorem fixedGeometry :
    (0x100000 : Addr).toNat + 8 * 2218 ≤ 2 ^ 64 ∧ (⟨0x100000, 8 * 2218⟩ : Region).Disjoint ⟨0x4000, 8448⟩ :=
  ⟨by decide, Region.disjoint_of_sep (by decide)⟩

private theorem satConsts (words : List (BitVec 64)) (size : words.length = 2218) :
    ConstsOk [(tableSym, words)] 0 (satState words) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [constRegs, Abi.constRegions, satState, List.map_cons, List.map_nil, size]
    rfl
  · intro c hc i hi
    obtain rfl := List.mem_singleton.mp hc
    exact constMem_held 0x100000 words (by rw [size]; decide) i hi
  · intro r hr
    simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    rw [size]
    refine ⟨fixedGeometry.1, ?_, ?_⟩
    · intro q hq
      change q ∈ ([⟨0x4000, 8448⟩] : List Region) at hq
      obtain rfl := List.mem_singleton.mp hq
      exact fixedGeometry.2
    · intro q hq
      change q ∈ ([] : List Region) at hq
      contradiction
  · intro r hr
    simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    exact (by decide : (0x100000 : BitVec 64).toNat % 64 = 0)

theorem sat : ∃ s, contract.pre s :=
  ⟨satState tableWords, pre_consts.mpr ⟨satPre tableWords,
    satConsts tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length⟩⟩

/-- `vg_ffdh_check_domain`, with the standard domains. -/
theorem verified : Verified RISCV64.target code contract := ⟨correct, constantTime, sat⟩

end VG.Proof.Ffdh.RISCV64.VettedValidation
