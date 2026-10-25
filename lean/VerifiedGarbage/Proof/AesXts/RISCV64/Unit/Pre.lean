module

public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Call
public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# XTS-AES of data units on RISCV64: the arguments of each call

The five calls of a whole-block function the functions make, each with
`XPre` from the precondition (`UPre`), for a state with the permissions
of the entry state and the call's arguments in its registers:

* `xpre_tweak`: the tweak value `i`, copied to the tweak (`tR`), enciphered
  with `tweak_schedule` from the zero second tweak (`zR`);
* `xpre_blocks`: the first `N` whole blocks of the data, from the tweak;
* `xpre_last`: the last whole block (`L`), from the tweak (`o = tO`) or from
  the second tweak (`o = zO`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64
open VG.Impl.AesXts.RISCV64Unit (tO zO wO)

theorem wrap_off (p : Addr) {d n k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d + n ≤ k) (hn : 0 < n := by decide) :
    (p + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

section
variable {s₀ s : State} (hp : UPre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
include hp hrd hwr

theorem xpre_tweak (a0 : s.gpr .a0 = K s₀) (a1 : s.gpr .a1 = BitVec.ofNat 64 (R s₀))
    (a2 : s.gpr .a2 = S s₀ + BitVec.ofNat 64 zO) (a3 : s.gpr .a3 = S s₀ + BitVec.ofNat 64 tO)
    (a4 : s.gpr .a4 = BitVec.ofNat 64 1) (a5 : s.gpr .a5 = Wk s₀) :
    XPre s (K s₀) (S s₀ + BitVec.ofNat 64 zO) (S s₀ + BitVec.ofNat 64 tO) (Wk s₀) 1 (R s₀) where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := hp.rounds
  n := by decide
  wt := hp.tsch_scr.sub_right (sub_trans z_sub tz_sub)
  wd := hp.tsch_scr.sub_right (sub_trans t_sub tz_sub)
  ws := hp.tsch_scr.sub_right wk_sub
  td := hp.t_z.symm
  ts := hp.z_wk
  ds := hp.t_wk
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := wrap_off _ hp.scr_wrap (by decide)
  wrapS := wrap_off _ hp.scr_wrap (by simp [wO])
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩

theorem xpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) (a0 : s.gpr .a0 = W s₀)
    (a1 : s.gpr .a1 = BitVec.ofNat 64 (R s₀)) (a2 : s.gpr .a2 = S s₀ + BitVec.ofNat 64 tO)
    (a3 : s.gpr .a3 = D s₀) (a4 : s.gpr .a4 = BitVec.ofNat 64 N) (a5 : s.gpr .a5 = Wk s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 tO) (D s₀) (Wk s₀) N (R s₀) where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := hp.rounds
  n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega
  wt := hp.sch_scr.sub_right (sub_trans t_sub tz_sub)
  wd := hp.sch_data.sub_right (Region.sub_prefix hN)
  ws := hp.sch_scr.sub_right wk_sub
  td := (hp.data_scr.symm.sub_left (sub_trans t_sub tz_sub)).sub_right (Region.sub_prefix hN)
  ts := hp.t_wk
  ds := (hp.data_scr.sub_left (Region.sub_prefix hN)).sub_right wk_sub
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := by have := hp.data_wrap; omega
  wrapS := wrap_off _ hp.scr_wrap (by simp [wO])
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩

theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) (a0 : s.gpr .a0 = W s₀)
    (a1 : s.gpr .a1 = BitVec.ofNat 64 (R s₀)) (a2 : s.gpr .a2 = S s₀ + BitVec.ofNat 64 o)
    (a3 : s.gpr .a3 = L s₀) (a4 : s.gpr .a4 = BitVec.ofNat 64 1) (a5 : s.gpr .a5 = Wk s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (Wk s₀) 1 (R s₀) := by
  have oS : Region.Sub ⟨S s₀ + BitVec.ofNat 64 o, 16⟩ (tzR s₀) := by
    rcases ho with rfl | rfl
    · exact t_sub
    · exact z_sub
  have oW : (⟨S s₀ + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint (wkR s₀) := by
    rcases ho with rfl | rfl
    · exact hp.t_wk
    · exact hp.z_wk
  have ol : o + 16 ≤ 2432 := by rcases ho with rfl | rfl <;> decide
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dataR s₀) := hp.l_sub
  exact {
    a0 := a0
    a1 := a1
    a2 := a2
    a3 := a3
    a4 := a4
    a5 := a5
    rounds := hp.rounds
    n := by decide
    wt := hp.sch_scr.sub_right (sub_trans oS tz_sub)
    wd := hp.sch_data.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := (hp.data_scr.symm.sub_left (sub_trans oS tz_sub)).sub_right lS
    ts := oW
    ds := (hp.data_scr.sub_left lS).sub_right wk_sub
    wrapT := wrap_off _ hp.scr_wrap ol
    wrapD := hp.l_wrap
    wrapS := wrap_off _ hp.scr_wrap (by simp [wO])
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega⟩
      · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega⟩
      · exact ⟨scrR s₀, by simp, wO, rfl, by simp [wO]⟩ }

end

end VG.Proof.AesXts.RISCV64.Unit
