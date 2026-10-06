import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseBytes

/-!
# Verification's static multiples of `-B`

`BaseTbl s base T`: the static at `T` holds the entries `baseByteCached` (`-[j + 1]B`,
cached) at `T + 128 j`, readable, and apart from the scratch at `base`, so that anything that
writes only the scratch keeps it (`BaseTbl.of_mem`). `baseAddr` computes an entry's address
from the static's address, which verification keeps at byte 7960 of the scratch, and
`pointFromTableQ` copies the entry there to slots 4–7 as it does from the scratch's tables.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs fe val4 F fe_st4 st4_outside Outside Keeps clob ea_at)
open VG.Impl.X25519.X86_64 (stores)

/-- The static's entries at `T`, readable and apart from the scratch at `base`. -/
structure BaseTbl (s : State) (base T : Addr) : Prop where
  entry : ∀ j < 255, tablePoint s.mem (off T (128 * j)) 0 =
    baseByteCached (baseBytesAffine.getD j (0, 1))
  read : ∀ d n, d + n ≤ 32640 → InRegions (s.rd ++ s.wr) (off T d) n
  far : ∀ i < 32640, 8192 ≤ ofs base (off T i)

theorem tablePoint_congr {m m' : Mem} {E : Addr}
    (h : ∀ i < 128, m' (off E i) = m (off E i)) : tablePoint m' E 0 = tablePoint m E 0 := by
  have hw : ∀ d, d + 8 ≤ 128 → Proof.X25519.X86_64.word m' E d = Proof.X25519.X86_64.word m E d :=
    fun d hd => Mem.readW_congr fun i hi => by
      rw [Offset.add_add]; exact h (d + i) (by omega)
  simp only [tablePoint, F, fe, hw _ (by omega : 0 + 8 ≤ 128)]
  rw [hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega),
    hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega),
    hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega)]

/-- The static survives any change of the memory at most 8192 bytes from `base`. -/
theorem BaseTbl.of_mem {s t : State} {base T : Addr} (h : BaseTbl s base T)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : ∀ p, 8192 ≤ ofs base p → t.mem p = s.mem p) : BaseTbl t base T := by
  refine ⟨fun j hj => ?_, fun d n hd => by rw [hrd, hwr]; exact h.read d n hd, h.far⟩
  rw [← h.entry j hj]
  refine tablePoint_congr fun i hi => hm _ ?_
  simp only [off, Offset.add_add]
  exact h.far _ (by omega)

theorem BaseTbl.of_outside {s t : State} {base T : Addr} {o n : Nat} (h : BaseTbl s base T)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : Outside base o n s.mem t.mem) (hn : o + n ≤ 8192) :
    BaseTbl t base T :=
  h.of_mem hrd hwr fun p hp => hm p (Or.inr (by omega))

/-! ## An entry's address -/

/-- `rax` = entry `j` of the static, whose address is at byte 7960 of the scratch. -/
theorem baseAddr_ok {s : State} {base T : Addr} (hs : Scratch s base)
    (hT : s.mem.readW (off base 7960) 64 = T) (j : Nat) (hj : j < 255)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block baseAddr) s fun t => t.gpr .rax = off T (128 * j) ∧ Keeps [.rax, .rcx, .rdx] s t := by
  have hval : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr : InRegions (s.rd ++ s.wr) (off base 7960) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide : 7960 + 8 ≤ 8192)
      (by have := hs.nowrap; omega)⟩
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
      env t.mem base ⟨4 + j, by omega⟩ = F s.mem E (32 * j) ∧
      TableKeep base (192 + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (fromStaticWords_ok hp (32 * j) fun k hk => hr _ (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores8192_ok ht.rdi ht.wr (by omega : 192 + 32 * j + 32 ≤ 8192)
    .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · change F u.mem base (64 + 32 * (4 + j)) = _
    rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega, F, hm, fe_st4 _ _ (by omega), hv]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromStaticPrefixQ_ok {s : State} {base E : Addr} (hs : Scratch s base)
    (hp : s.gpr .rax = E) (hr : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off E d) 8)
    (hE : ∀ i < 128, 8192 ≤ ofs base (off E i)) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨4 + j, by omega⟩ = F s.mem E (32 * j)) ∧
      TableKeep base 192 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp hr (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (fromStaticQuarterQ_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega)
      (fun d hd => by rw [hk.rd, hk.wr]; exact hr d hd)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨4 + j, by omega⟩ = env t.mem base ⟨4 + j, by omega⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu]
      simp only [F, fe, Proof.X25519.X86_64.word]
      have hw : ∀ d, d + 8 ≤ 128 → t.mem.readW (off E d) 64 = s.mem.readW (off E d) 64 :=
        fun d hd => Mem.readW_congr fun i hi => by
          rw [Offset.add_add]
          exact hk.mem (off E (d + i)) (Or.inr (by have := hE (d + i) (by omega); omega))
      rw [hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega)]

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

end VG.Proof.Ed25519.X86_64
