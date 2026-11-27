module

public import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarStep
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.X25519.X86_64.Setup
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
public import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
public import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
import VerifiedGarbage.Proof.Ed25519.Bytes

/-! ### `Ed25519.X86_64.DecodeBits`, which this module and modules that import it used -/

section

/-! Load the encoded y-coordinate and its separate sign bit. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps ea_at val4)

theorem decodeLE_inputWords (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) =
      val4 (m.readW (off p 0) 64) (m.readW (off p 8) 64)
        (m.readW (off p 16) 64) (m.readW (off p 24) 64) := by
  rw [decodeLE_eq, show off p 0 = p from BitVec.add_zero p, val4]
  exact VG.Proof.X25519.leNum_bytesAt_words64 m p

private theorem encoded_top (m : Mem) (p : Addr) :
    ((m.readW (off p 24) 64) >>> 63).toNat =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) / 2 ^ 255 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, decodeLE_inputWords, val4]
  have h0 := (m.readW (off p 0) 64).isLt
  have h1 := (m.readW (off p 8) 64).isLt
  have h2 := (m.readW (off p 16) 64).isLt
  omega_using []

theorem loadSign_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : InRegions (s.rd ++ s.wr) (off p 24) 8) :
    WP isa (.block loadSign) s fun t =>
      t.gpr .rsi = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      Keeps [.rsi] s t := by
  have hn := decodeLE_lt (Spec.Ed25519.bytesAt s.mem p 32)
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [hl] at hn
  have hv : (s.mem.readW (off p 24) 64) >>> 63 =
      signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) := by
    have h : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 = 0 ∨
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 = 1 := by omega_using [hn]
    apply BitVec.eq_of_toNat_eq
    rw [encoded_top]
    rcases h with h | h <;> rw [h] <;> rfl
  apply WP.of_runBlock
  simp only [loadSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift,
    State.load64, ea_at, hp, hr, show 1 ≤ 63 ∧ 63 ≤ 63 by decide, and_self,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

theorem loadY_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block Impl.X25519.X86_64.loadU) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 ∧
      Keeps [.r8, .r9, .r10, .r11, .rax] s t := by
  refine WP.mono (Proof.X25519.X86_64.loadU_ok s hp hr) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, kt⟩
  rw [tv, Proof.X25519.decodeUCoordinate_eq (Proof.X25519.length_bytesAt _ _ _), decodeLE_eq]
  rfl

end VG.Proof.Ed25519.X86_64

end

end

/-! ### `Ed25519.X86_64.BaseEntry`, which the modules that import this one used -/

section

/-!
# Verification's static odd multiples of `B`

`BaseTbl s base T`: the static at `T` holds the entries `baseOddCached` (`[dec (j + 1)](-B)`,
cached) at `T + 128 j`, readable, and apart from the scratch at `base`, so that anything that
writes only the scratch keeps it (`BaseTbl.of_mem`). `baseAddr` computes an entry's address
from the static's address, which verification keeps at byte 7960 of the scratch, and
`pointFromTableQ` copies the entry there to slots 4–7 as it does from the scratch's tables.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs fe val4 F fe_st4 st4_outside Outside Keeps clob ea_at)
open VG.Impl.X25519.X86_64 (stores)

/-- The static's entries at `T`, readable and apart from the scratch at `base`. -/
structure BaseTbl (s : State) (base T : Addr) : Prop where
  entry : ∀ j < 128, tablePoint s.mem (off T (128 * j)) 0 =
    baseOddCached (baseOddAffine.getD j (0, 1))
  read : ∀ d n, d + n ≤ 16384 → InRegions (s.rd ++ s.wr) (off T d) n
  far : ∀ i < 16384, 8192 ≤ ofs base (off T i)

theorem tablePoint_congr {m m' : Mem} {E : Addr}
    (h : ∀ i < 128, m' (off E i) = m (off E i)) : tablePoint m' E 0 = tablePoint m E 0 := by
  have hw : ∀ d, d + 8 ≤ 128 → Proof.X25519.X86_64.word m' E d = Proof.X25519.X86_64.word m E d :=
    fun d hd => Mem.readW_congr fun i hi => by
      rw [Offset.add_add]; exact h (d + i) (by omega_using [hd, hi])
  simp only [tablePoint, F, fe, hw _ (by omega_using [] : 0 + 8 ≤ 128)]
  rw [hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using []),
    hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using []),
    hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using []), hw _ (by omega_using [])]

/-- The static survives any change of the memory at most 8192 bytes from `base`. -/
theorem BaseTbl.of_mem {s t : State} {base T : Addr} (h : BaseTbl s base T)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : ∀ p, 8192 ≤ ofs base p → t.mem p = s.mem p) : BaseTbl t base T := by
  refine ⟨fun j hj => ?_, fun d n hd => by rw [hrd, hwr]; exact h.read d n hd, h.far⟩
  rw [← h.entry j hj]
  refine tablePoint_congr fun i hi => hm _ ?_
  simp only [off, Offset.add_add]
  exact h.far _ (by omega_using [hj, hi])

theorem BaseTbl.of_outside {s t : State} {base T : Addr} {o n : Nat} (h : BaseTbl s base T)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : Outside base o n s.mem t.mem) (hn : o + n ≤ 8192) :
    BaseTbl t base T :=
  h.of_mem hrd hwr fun p hp => hm p (Or.inr (by omega_using [hn, hp]))

/-! ## An entry's address -/

/-- `rax` = entry `j` of the static, whose address is at byte 7960 of the scratch. -/
theorem baseAddr_ok {s : State} {base T : Addr} (hs : Scratch s base)
    (hT : s.mem.readW (off base 7960) 64 = T) (j : Nat) (hj : j < 128)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block baseAddr) s fun t => t.gpr .rax = off T (128 * j) ∧ Keeps [.rax, .rcx, .rdx] s t := by
  have hval : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj])]
  have hr : InRegions (s.rd ++ s.wr) (off base 7960) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide : 7960 + 8 ≤ 8192)
      (by have := hs.nowrap; omega_using [])⟩
  rw [baseAddr, show ([.mov .rax (.reg .rbx), .movImm64 .rcx 128, .mul .rcx,
      .mov .rcx (.mem (Impl.X25519.X86_64.sc 7960)), .alu .add .rax (.reg .rcx)] : List Instr) =
    [.mov .rax (.reg .rbx), .movImm64 .rcx 128, .mul .rcx] ++
      ([.mov .rcx (.mem (Impl.X25519.X86_64.sc 7960))] ++ [.alu .add .rax (.reg .rcx)]) from rfl,
    WP.block_append_iff]
  have h1 : WP isa (.block [.mov .rax (.reg .rbx), .movImm64 .rcx 128, .mul .rcx]) s fun a =>
      a.gpr .rax = BitVec.ofNat 64 (128 * j) ∧ Keeps [.rax, .rcx, .rdx] s a := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
      RegUpd.gpr_setReg, hc, hval, ite_true, ite_false, reduceCtorEq,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨by rw [Nat.mul_comm]; rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  refine WP.mono h1 fun a ⟨ha, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hra : InRegions (a.rd ++ a.wr) (off base 7960) 8 := by rw [ka.2.2.1, ka.2.2.2]; exact hr
  have har : a.gpr .rdi = base := (ka.1 _ (by decide)).trans hs.rdi
  have h2 : WP isa (.block [.mov .rcx (.mem (Impl.X25519.X86_64.sc 7960))]) a fun b =>
      b.gpr .rcx = T ∧ Keeps [.rcx] a b := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
      Proof.X25519.X86_64.ea_sc, har, hra, ite_true, Option.map_some, Option.some.injEq,
      exists_eq_left', RegUpd.gpr_setReg_self]
    refine ⟨by rw [ka.2.1, hT], fun k hk => ?_, rfl, rfl, rfl⟩
    exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hk)
  refine WP.mono h2 fun b ⟨hb, kb⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => ?_, kb.2.1.trans ka.2.1, kb.2.2.1.trans ka.2.2.1, kb.2.2.2.trans ka.2.2.2⟩
  · rw [hb, kb.1 _ (by decide), ha, BitVec.add_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, ite_false]
    rw [kb.1 r (by simp [hr.2.1]), ka.1 r (by simp [hr.1, hr.2.1, hr.2.2])]

/-! ## An entry to slots 4–7 -/

/-- The four words at `E + src`, readable, into `r8–r11`. -/
theorem fromStaticWords_ok {s : State} {E : Addr} (hp : s.gpr .rax = E) (src : Nat)
    (hr : ∀ k < 4, InRegions (s.rd ++ s.wr) (off E (src + 8 * k)) 8) :
    WP isa (.block (fromTableWords src)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem E src ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  apply WP.of_runBlock
  simp only [fromTableWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hp, r0, r1, r2, r3, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem fromStaticQuarterQ_ok {s : State} {base E : Addr} (hs : Scratch s base)
    (hp : s.gpr .rax = E) (j : Nat) (hj : j < 4)
    (hr : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off E d) 8) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      env t.mem base ⟨4 + j, by omega_using [hj]⟩ = F s.mem E (32 * j) ∧
      TableKeep base (192 + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (fromStaticWords_ok hp (32 * j) fun k hk => hr _ (by omega_using [hj, hk])) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores8192_ok ht.rdi ht.wr (by omega_using [hj] : 192 + 32 * j + 32 ≤ 8192)
    .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · change F u.mem base (64 + 32 * (4 + j)) = _
    rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega_using [], F, hm, fe_st4 _ _ (by omega_using [hj]), hv]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega_using [hj]) _ _ _ _

theorem fromStaticPrefixQ_ok {s : State} {base E : Addr} (hs : Scratch s base)
    (hp : s.gpr .rax = E) (hr : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off E d) 8)
    (hE : ∀ i < 128, 8192 ≤ ofs base (off E i)) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨4 + j, by omega_using [hn, hj]⟩ = F s.mem E (32 * j)) ∧
      TableKeep base 192 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp hr (by omega_using [hn])) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (fromStaticQuarterQ_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega_using [hn])
      (fun d hd => by rw [hk.rd, hk.wr]; exact hr d hd)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega_using []) (by omega_using [])).trans
      (ku.mono (by omega_using []) (by omega_using []))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨4 + j, by omega_using [hn, hj]⟩ = env t.mem base ⟨4 + j, by omega_using [hn, hj]⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega_using [hn, hj]) (Or.inl (by simp only [offset]; omega_using [h]))
      rw [he, hv j h]
    · have he : j = n := by omega_using [hj, h]
      subst j
      rw [hu]
      simp only [F, fe, Proof.X25519.X86_64.word]
      have hw : ∀ d, d + 8 ≤ 128 → t.mem.readW (off E d) 64 = s.mem.readW (off E d) 64 :=
        fun d hd => Mem.readW_congr fun i hi => by
          rw [Offset.add_add]
          exact hk.mem (off E (d + i)) (Or.inr (by have := hE (d + i) (by omega_using [hd, hi]); omega_using [hn, this]))
      rw [hw _ (by omega_using [hn]), hw _ (by omega_using [hn]), hw _ (by omega_using [hn]), hw _ (by omega_using [hn])]

/-- The entry at `E`, readable and apart from the scratch, to slots 4–7. -/
theorem pointFromStaticQ_ok {s : State} {base E : Addr} (hs : Scratch s base)
    (hp : s.gpr .rax = E) (hr : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off E d) 8)
    (hE : ∀ i < 128, 8192 ≤ ofs base (off E i)) :
    WP isa (.block pointFromTableQ) s fun t =>
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem E 0 ∧ TableKeep base 192 128 s t := by
  refine WP.mono (fromStaticPrefixQ_ok hs hp hr hE 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  change env t.mem base 4 = _ at h0
  change env t.mem base 5 = _ at h1
  change env t.mem base 6 = _ at h2
  change env t.mem base 7 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3, Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul]

theorem BaseTbl.of_powers {s t : State} {base T : Addr} {o n : Nat} (h : BaseTbl s base T)
    (k : PowersKeep base o n s t) (hn : o + n ≤ 8192) : BaseTbl t base T :=
  h.of_mem k.rd k.wr fun p hp => k.mem p (by omega_using [hp]) (Or.inr (by omega_using [hn, hp]))

end VG.Proof.Ed25519.X86_64

end

end

/-!
# Verification preserves its inputs and saved pointers

Apart from the windows' group facts (`WindowStep`), so that verification's context
(`VerifyContext`) need not import the group's algebra.
-/

@[expose] public section

section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside)

theorem tableFrame_work {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : o ≤ 64) (hn : 768 ≤ o + n) : Outside base o n m m' :=
  fun p hp => h p (by omega_using [ho, hn, hp]) hp

theorem outside_bytes {base p : Addr} {o n len : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192)
    (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt m' p len = Spec.Ed25519.bytesAt m p len := by
  apply List.map_congr_left
  intro i hi
  apply h
  change ofs base (off p i) < o ∨ o + n ≤ ofs base (off p i)
  have := hf i (List.mem_range.mp hi)
  omega_using [hn, this]

theorem PowersKeep.header {base : Addr} {o n d : Nat} {s t : State}
    (h : PowersKeep base o n s t) (hd : 7936 ≤ d) (hb : d + 8 ≤ 8192) (hn : o + n ≤ 7936) :
    t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (by omega_using [hd]) (Or.inr (by omega_using [hd, hn])) (by omega_using [hb])

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyInputs`. -/
section
/-! Reload verification pointers and check the complete unsigned scalar S. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Proof.X25519.X86_64 (off Keeps ea_at ea_sc val4)

theorem loadPointer_ok {s : State} {base : Addr} (hs : Scratch s base) (r : Reg) (d : Nat)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega_using [hd])⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_sc, hs.rdi, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hk)

theorem add32_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add r (.imm 32)]) s fun t => t.gpr r = off (s.gpr r) 32 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨rfl, fun k hk => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show k ≠ r by simpa only [List.mem_singleton] using hk, ite_false]

theorem loadScalarWords_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadScalarWords) s fun t =>
      scalarValue t = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [loadScalarWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hp, hr 0 (by decide), hr 8 (by decide), hr 16 (by decide), hr 24 (by decide),
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left', scalarValue]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact (decodeLE_inputWords s.mem p).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem verifyScalar_ok {s : State} {base sig : Addr} (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8) :
    WP isa (.block verifyScalar) s fun t => Keep base s t ∧ t.mem = s.mem ∧
      t.cf = some (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) < Spec.Ed25519.L)) := by
  change WP isa (.block (([.mov .rdx (.mem (sc 7944))] : List Instr) ++
    ([.alu .add .rdx (.imm 32)] : List Instr) ++ loadScalarWords ++ scalarSubtract)) s _
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rdx 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_
  rw [hp] at ap
  rw [WP.block_append_iff]
  refine WP.mono (add32_ok a .rdx) fun b ⟨bp, kb⟩ => ?_
  rw [ap] at bp
  rw [WP.block_append_iff]
  refine WP.mono (loadScalarWords_ok b (off sig 32) bp (by
    intro d hd; rw [kb.2.2.1, kb.2.2.2, ka.2.2.1, ka.2.2.2]; exact hr d hd)) fun c ⟨cv, kc⟩ => ?_
  refine WP.mono (scalarSubtract_ok c) fun t ⟨tc, _, _, kt⟩ => ?_
  refine ⟨(((Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kb (by decide))).trans
    (Keep.of_keeps kc (by decide))).trans (Keep.of_keeps kt (by decide)),
    kt.2.1.trans (kc.2.1.trans (kb.2.1.trans ka.2.1)), ?_⟩
  rw [tc, cv, kb.2.1, ka.2.1]

end VG.Proof.Ed25519.X86_64
end
