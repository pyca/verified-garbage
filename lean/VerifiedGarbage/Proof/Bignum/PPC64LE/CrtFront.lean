module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSave
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtArgs
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: the front

`front_ok`: `save`, `args` and `setupX`: the nonvolatile registers saved,
the arguments in the header and `X`'s registers (`Front`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The working space. -/
abbrev cS (s : State) : Addr := stackArg s 8
/-- Its size in bytes. -/
abbrev cZ (s : State) : Nat := (stackArg s 9).toNat * 8
/-- `k`. -/
abbrev ck (s : State) : Nat := (s.gpr .r6).toNat
/-- `X`'s words. -/
abbrev cwX (s : State) : Nat := 2 * ((ck s + 7) / 8)
/-- `p`'s length. -/
abbrev cpL (s : State) : Nat := (s.gpr .r10).toNat
/-- `q`'s length. -/
abbrev cqL (s : State) : Nat := (stackArg s 1).toNat

/-- The registers the front writes. -/
def frontRegs : List Reg := [.r0, .r3, .r4, .r5, .r10, .r11, .r21, .r23, .r27, .r28, .r29]

/-- What holds after the front, from the entry state `s₀`. -/
structure Front (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : word s.mem (cS s₀) oOut = off (s₀.gpr .r3) 0
  hN : word s.mem (cS s₀) oN = off (s₀.gpr .r5) 0
  hNL : word s.mem (cS s₀) oNLen = BitVec.ofNat 64 (ck s₀)
  hIn : word s.mem (cS s₀) oIn = off (s₀.gpr .r7) 0
  hP : word s.mem (cS s₀) oP = off (s₀.gpr .r9) 0
  hPL : word s.mem (cS s₀) oPLen = BitVec.ofNat 64 (cpL s₀)
  hQ : word s.mem (cS s₀) oQ = off (stackArg s₀ 0) 0
  hQL : word s.mem (cS s₀) oQLen = BitVec.ofNat 64 (cqL s₀)
  hDP : word s.mem (cS s₀) oDP = off (stackArg s₀ 2) 0
  hDQ : word s.mem (cS s₀) oDQ = off (stackArg s₀ 4) 0
  hQI : word s.mem (cS s₀) oQInv = off (stackArg s₀ 6) 0
  hBP : word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : word s.mem (cS s₀) oBQ = off (cS s₀) (slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 8)
  r23 : s.gpr .r23 = cS s₀
  r10 : s.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0)
  r21 : s.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀)
  r27 : s.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  keep : Keep frontRegs s₀ s
  sav : ∀ i < 18, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  mem : Outside (cS s₀) 0 256 s₀.mem s.mem

theorem frame_sub {m m' : Mem} {B : Addr} {o n : Nat} (h : Frame [⟨off B o, n⟩] m m') (ho : o + n ≤ 2 ^ 64)
    (hn : 0 < n) :
    Outside B o n m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  have e := ofs_rebase B x (o := o) (by omega)
  change ofs (off B o) x + 1 ≤ n at hc
  change ofs B x < o ∨ o + n ≤ ofs B x at hx
  rcases e with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

theorem saved_ne11 : ∀ i < 18, Crt.saved i ≠ .r11 := by decide

theorem front_ok (s₀ : State) (h : fnContract.pre s₀) :
    WP isa (.block (Crt.save ++ Crt.args ++ setupX)) s₀ (Front s₀) := by
  obtain ⟨hsp, hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hk1 := (s₀.gpr .r6).isLt
  have hscr : Scr s₀ (cS s₀) (cZ s₀) := Scr.of_mem (by rw [hwr]; simp) nwS
  have hn := hscr.nowrap
  have hZ : 128 * ck s₀ + 256 ≤ cZ s₀ := by
    show 128 * (s₀.gpr .r6).toNat + 256 ≤ (stackArg s₀ 9).toNat * 8; omega
  have hargs : (⟨stackArgAddr s₀ 0, 80⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have sa : ∀ i, stackArgAddr s₀ i = stackArgAddr s₀ 0 + BitVec.ofNat 64 (8 * i) := fun i => by
    simp only [stackArgAddr]; rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hst : ∀ i < 10, InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ i) 8 := fun i hi =>
    ⟨_, List.mem_append_left _ hargs, by rw [sa i]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hsep : ∀ j < 10, ∀ i < 8, ∀ x, ofs (cS s₀) x < cZ s₀ → stackArgAddr s₀ j + BitVec.ofNat 64 i ≠ x :=
    fun j hj i hi x hx e => by
      subst e
      refine dSA _ (by
        change ((stackArgAddr s₀ j + BitVec.ofNat 64 i) - cS s₀).toNat + 1 ≤ cZ s₀
        change ((stackArgAddr s₀ j + BitVec.ofNat 64 i) - cS s₀).toNat < cZ s₀ at hx; omega) ?_
      rw [sa j, Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
  have hsavR : ∀ i < 18, (⟨cS s₀, cZ s₀⟩ : Region).Contains (off (savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ (hst 8 (by decide)) fun i hi => ⟨_, by rw [hwr]; simp, hsavR i hi⟩)
    fun t ⟨s₁, a11, m1, k1, hSv⟩ => ?_
  have kt := k1.trans hSv.keep
  have t23 : t.gpr .r23 = cS s₀ := hSv.r23.trans a11
  have tsp : ∀ i, stackArgAddr t i = stackArgAddr s₀ i := fun i => by simp only [stackArgAddr, kt.sp]
  have fr : Frame [savR (savW (cS s₀))] s₀.mem t.mem := by
    have := hSv.frame; rw [a11, m1] at this; exact this
  have savSub : Region.Sub (savR (savW (cS s₀))) ⟨cS s₀, cZ s₀⟩ := Offset.sub_base _ (by omega)
  have tst : ∀ i < 10, stackArg t i = stackArg s₀ i := fun i hi => by
    simp only [stackArg, tsp]
    refine fr.readW (r := ⟨stackArgAddr s₀ i, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr
    subst hr
    have argSub : Region.Sub ⟨stackArgAddr s₀ i, 8⟩ ⟨stackArgAddr s₀ 0, 80⟩ := by
      rw [sa i]; exact Offset.sub_base _ (by omega)
    exact (dSA.symm.sub_left argSub).sub_right savSub
  rw [WP.block_append_iff]
  refine WP.mono (args_ok (hscr.congr kt.wr) (by omega) t23 (fun i hi => by rw [tsp, kt.rd, kt.wr]; exact hst i hi)
    (fun j hj i hi x hx => by rw [tsp]; exact hsep j hj i hi x hx))
    fun u ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, Ou⟩, ku⟩ => ?_
  have ktu := kt.trans ku
  refine WP.mono (setupX_ok (k := ck s₀) (pL := cpL s₀) (hscr.congr ktu.wr) (by omega) ((ku.gpr _ (by decide)).trans t23)
    (by rw [ktu.gpr _ (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm) hk'
    (by rw [w5, kt.gpr _ (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm) hp1
    (by show (s₀.gpr .r10).toNat < 2 ^ 60; omega))
    fun v ⟨⟨v10, v21, v29, v11, v27, v28, vBP, vBQ, Ov⟩, kv⟩ => ?_
  have k := ktu.trans kv
  have hw : ∀ d, d + 8 ≤ 96 → word v.mem (cS s₀) d = word u.mem (cS s₀) d := fun d hd =>
    Ov.word (Or.inl hd) (by omega)
  have z : ∀ x : Addr, x = off x 0 := fun x => (BitVec.add_zero x).symm
  refine ⟨hscr.congr k.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, vBP, vBQ, (kv.gpr _ (by decide)).trans
    ((ku.gpr _ (by decide)).trans t23), v10, v21, v29, v11, v27, v28, k.mono, fun i hi => ?_, ?_⟩
  · rw [hw _ (by decide), w0, kt.gpr _ (by decide)]; exact z _
  · rw [hw _ (by decide), w1, kt.gpr _ (by decide)]; exact z _
  · rw [hw _ (by decide), w2, kt.gpr _ (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  · rw [hw _ (by decide), w3, kt.gpr _ (by decide)]; exact z _
  · rw [hw _ (by decide), w4, kt.gpr _ (by decide)]; exact z _
  · rw [hw _ (by decide), w5, kt.gpr _ (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  · rw [hw _ (by decide), w6, tst 0 (by decide)]; exact z _
  · rw [hw _ (by decide), w7, tst 1 (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  · rw [hw _ (by decide), w8, tst 2 (by decide)]; exact z _
  · rw [hw _ (by decide), w9, tst 4 (by decide)]; exact z _
  · rw [hw _ (by decide), w10, tst 6 (by decide)]; exact z _
  · have hs1 := hSv.saved i hi
    rw [a11, k1.gpr _ (fun h => saved_ne11 i hi (List.mem_singleton.mp h))] at hs1
    change t.mem.readW (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 64 = _ at hs1
    change v.mem.readW (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [Offset.add_add] at hs1 ⊢
    have h1 := Ov.word (d := 112 + 8 * i) (Or.inr (by omega)) (by omega)
    have h2 := Ou.word (d := 112 + 8 * i) (Or.inr (by omega)) (by omega)
    simp only [word] at h1 h2
    rw [h1, h2]; exact hs1
  · exact (((frame_sub (o := 112) fr (by omega) (by decide)).mono (by omega) (by omega)).trans
      (Ou.mono (by omega) (by omega))).trans (Ov.mono (by omega) (by omega))

end VG.Proof.Bignum.PPC64LE.Crt
