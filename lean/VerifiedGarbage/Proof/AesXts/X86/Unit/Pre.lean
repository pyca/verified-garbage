module

public import VerifiedGarbage.Proof.AesXts.X86.Unit.Call
public import VerifiedGarbage.Proof.AesXts.X86.Unit.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# XTS-AES of data units on x86: the arguments of each call

The five calls of a whole-block function the functions make, each with
`XPre` from the precondition (`UPre`), for a state with the permissions and
stack pointer of the entry state and the call's arguments in its registers:

* `xpre_tweak`: the tweak value `i`, copied to the tweak (`tR`), enciphered
  with `tweak_schedule` from the zero second tweak (`zR`);
* `xpre_blocks`: the first `N` whole blocks of the data, from the tweak;
* `xpre_last`: the last whole block (`L`), from the tweak (`o = tO`) or from
  the second tweak (`o = zO`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86
open VG.Impl.AesXts.X86Unit (tO zO)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrN {d : Nat} (hd : d < 2432) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem UPre.dataN {d : Nat} (hd : d < Len s₀) : (D s₀ + BitVec.ofNat 32 d).toNat = (D s₀).toNat + d := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The last whole block, as a register holds it. -/
abbrev Lv (s₀ : State) : BitVec 32 := D s₀ + BitVec.ofNat 32 (16 * (M s₀ - 1))

theorem UPre.lA : (Lv s₀).setWidth 64 = L s₀ :=
  hp.dataA (by have := len_eq s₀; have := hp.m_pos; omega)

theorem UPre.scrW {d : Nat} (hd : d < 2432) : (S s₀ + BitVec.ofNat 32 d).setWidth 64 = Sa s₀ + BitVec.ofNat 64 d :=
  hp.scrA hd

theorem UPre.stk_eq {s : State} (hsp : s.gpr .esp = s₀.gpr .esp) : below (s.gpr .esp) 52 = stkR s₀ := by
  rw [hsp]; simp only [below]; rw [Taint.sub_setWidth hp.esp52]

theorem UPre.cS (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (Sa s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by have := hp.scr_wrap; omega)

end

section
variable {s₀ s : State} (hp : UPre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.gpr .esp = s₀.gpr .esp)
include hp hrd hwr hsp

theorem xpre_tweak (eax : s.gpr .eax = K s₀) (ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀))
    (edx : s.gpr .edx = S s₀ + BitVec.ofNat 32 zO) (ebx : s.gpr .ebx = S s₀ + BitVec.ofNat 32 tO)
    (edi : s.gpr .edi = BitVec.ofNat 32 1) (ebp : s.gpr .ebp = S s₀) :
    XPre s (K s₀) (S s₀ + BitVec.ofNat 32 zO) (S s₀ + BitVec.ofNat 32 tO) (S s₀) 1 (R s₀) := by
  have aT := hp.scrW (d := tO) (by decide)
  have aZ := hp.scrW (d := zO) (by decide)
  have stk := hp.stk_eq hsp
  exact {
    eax := eax
    ecx := ecx
    edx := edx
    ebx := ebx
    edi := edi
    ebp := ebp
    rounds := hp.rounds
    n := by decide
    esp52 := by rw [hsp]; exact hp.esp52
    wt := by rw [aZ]; exact hp.tsch_scr.sub_right (sub_trans z_sub s_sub)
    wd := by rw [aT]; exact hp.tsch_scr.sub_right (sub_trans t_sub s_sub)
    ws := hp.tsch_scr.sub_right wk_sub
    td := by rw [aZ, aT]; exact hp.t_z.symm
    ts := by rw [aZ]; exact hp.z_wk
    ds := by rw [aT]; exact hp.t_wk
    bw := by rw [stk]; exact hp.stk_tsch
    bt := by rw [stk, aZ]; exact hp.stk_scr.sub_right (sub_trans z_sub s_sub)
    bd := by rw [stk, aT]; exact hp.stk_scr.sub_right (sub_trans t_sub s_sub)
    bs := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.tsch_fit
    fitT := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [zO]; omega
    fitD := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [tO]; omega
    fitS := by have := hp.scr_fit; omega
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aZ, aT]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
      · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

theorem xpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) (eax : s.gpr .eax = W s₀)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)) (edx : s.gpr .edx = S s₀ + BitVec.ofNat 32 tO)
    (ebx : s.gpr .ebx = D s₀) (edi : s.gpr .edi = BitVec.ofNat 32 N) (ebp : s.gpr .ebp = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 32 tO) (D s₀) (S s₀) N (R s₀) := by
  have aT := hp.scrW (d := tO) (by decide)
  have stk := hp.stk_eq hsp
  have dS : Region.Sub ⟨(D s₀).setWidth 64, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  exact {
    eax := eax
    ecx := ecx
    edx := edx
    ebx := ebx
    edi := edi
    ebp := ebp
    rounds := hp.rounds
    n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega
    esp52 := by rw [hsp]; exact hp.esp52
    wt := by rw [aT]; exact hp.sch_scr.sub_right (sub_trans t_sub s_sub)
    wd := hp.sch_data.sub_right dS
    ws := hp.sch_scr.sub_right wk_sub
    td := by rw [aT]; exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right dS
    ts := by rw [aT]; exact hp.t_wk
    ds := (hp.data_scr.sub_left dS).sub_right wk_sub
    bw := by rw [stk]; exact hp.stk_sch
    bt := by rw [stk, aT]; exact hp.stk_scr.sub_right (sub_trans t_sub s_sub)
    bd := by rw [stk]; exact hp.stk_data.sub_right dS
    bs := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.sch_fit
    fitT := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [tO]; omega
    fitD := by have := hp.data_fit; omega
    fitS := by have := hp.scr_fit; omega
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aT]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
      · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) (eax : s.gpr .eax = W s₀)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)) (edx : s.gpr .edx = S s₀ + BitVec.ofNat 32 o)
    (ebx : s.gpr .ebx = Lv s₀) (edi : s.gpr .edi = BitVec.ofNat 32 1) (ebp : s.gpr .ebp = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 32 o) (Lv s₀) (S s₀) 1 (R s₀) := by
  have ol : o + 16 ≤ 2208 := by rcases ho with rfl | rfl <;> decide
  have aO := hp.scrW (d := o) (by omega)
  have aL := hp.lA
  have stk := hp.stk_eq hsp
  have oS : Region.Sub ⟨Sa s₀ + BitVec.ofNat 64 o, 16⟩ ⟨Sa s₀, 2208⟩ := Offset.sub_base _ ol
  have oW : (⟨Sa s₀ + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint (wkR s₀) := by
    rcases ho with rfl | rfl
    · exact hp.t_wk
    · exact hp.z_wk
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dataR s₀) := hp.l_sub
  exact {
    eax := eax
    ecx := ecx
    edx := edx
    ebx := ebx
    edi := edi
    ebp := ebp
    rounds := hp.rounds
    n := by decide
    esp52 := by rw [hsp]; exact hp.esp52
    wt := by rw [aO]; exact hp.sch_scr.sub_right (sub_trans oS s_sub)
    wd := by rw [aL]; exact hp.sch_data.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := by rw [aO, aL]; exact (hp.data_scr.symm.sub_left (sub_trans oS s_sub)).sub_right lS
    ts := by rw [aO]; exact oW
    ds := by rw [aL]; exact (hp.data_scr.sub_left lS).sub_right wk_sub
    bw := by rw [stk]; exact hp.stk_sch
    bt := by rw [stk, aO]; exact hp.stk_scr.sub_right (sub_trans oS s_sub)
    bd := by rw [stk, aL]; exact hp.stk_data.sub_right lS
    bs := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.sch_fit
    fitT := by rw [hp.scrN (by omega)]; have := hp.scr_fit; omega
    fitD := by
      have := hp.l_wrap
      rw [← aL, addr_toNat] at this
      omega
    fitS := by have := hp.scr_fit; omega
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aO, aL]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simp; omega⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

end

end VG.Proof.AesXts.X86.Unit
