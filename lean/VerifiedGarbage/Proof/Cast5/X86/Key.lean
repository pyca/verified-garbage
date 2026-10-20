module
public import VerifiedGarbage.Proof.Cast5.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Cast5.X86.KeyHalf
import VerifiedGarbage.Proof.Cast5.X86.Ecb
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CAST5 key expansion on 32-bit x86

`expandKey` saves the callee-saved registers in the working space, pads the
key with zeros into `x` (§2.5), runs both halves of §2.4 and restores the
registers (`key_correct`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86
open VG.Proof.Cast5 (XZ HoldsXZ Keys KMem off_lt halves halves_length halves_two bytesAt_getD scheduleAt_keys
  byte_write Held)

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_byte32 (m : Mem) (c : Addr) {d e : Nat} (hd : d + 4 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (0 : BitVec 32)) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 4 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

/-- The memory after `x` := zeros. -/
def zeroMem (m : Mem) (S : BitVec 32) : Mem :=
  (((m.writeW (addr S xOff) (0 : BitVec 32)).writeW (addr S (xOff + 4)) (0 : BitVec 32)).writeW
    (addr S (xOff + 8)) (0 : BitVec 32)).writeW (addr S (xOff + 12)) (0 : BitVec 32)

theorem zeroMem_cinv (m : Mem) {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) (key : Addr) :
    CInv m key (S.setWidth 64) 0 (zeroMem m S) := by
  have e (d : Nat) (hd : d < 256) := addr_off hfit d hd
  simp only [zeroMem, xOff]
  rw [e 16 (by decide), e 20 (by decide), e 24 (by decide), e 28 (by decide)]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [zero_byte32 _ _ (by decide) (by omega), zero_byte32 _ _ (by decide) (by omega),
      zero_byte32 _ _ (by decide) (by omega), zero_byte32 _ _ (by decide) (by omega)]
    repeat' split
    all_goals first | rfl | omega
  · rw [zero_byte32 _ _ (by decide) (by omega), zero_byte32 _ _ (by decide) (by omega),
      zero_byte32 _ _ (by decide) (by omega), zero_byte32 _ _ (by decide) (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))

theorem copyStep_ok (u : State) {m0 : Mem} {key c : Addr} {k32 x32 : BitVec 32} {j : Nat} (hj : j < 16)
    (hI : CInv m0 key c j u.mem) (hdi : u.gpr .edi = k32) (hax : u.gpr .eax = x32)
    (ek : addr k32 0 = key + BitVec.ofNat 64 j) (ex : addr x32 0 = c + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (key + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (c + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (key + BitVec.ofNat 64 j) = m0 (key + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 key c (j + 1) v.mem ∧ v.gpr .edi = k32 + 1 ∧ v.gpr .eax = x32 + 1 ∧ v.gpr .ebx = u.gpr .ebx - 1 ∧
      v.zf = some (u.gpr .ebx - 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ebx → r ≠ .ecx → v.gpr r = u.gpr r) ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms := by
  unfold copyStep
  crun [hdi, hax, ek, ex, hr, hw, hk]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 => ?_⟩
  · simp only [Mem.writeW]
    rw [byte_write (d := 16 + j) (e := 16 + i) (n := 1) _ _ _ (by omega) (by omega)]
    split
    · have hij : i = j := by omega
      subst hij
      rw [Nat.sub_self, ite_eq_left (show i < i + 1 by omega), ite_eq_left (show Reg8.cl.reg = Reg.ecx from rfl)]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [hI.x i hi]
      split <;> split <;> first | rfl | omega
  · simp only [Mem.writeW]
    rw [byte_write (d := 16 + j) (e := 32 + i) (n := 1) _ _ _ (by omega) (by omega), ite_eq_right (by omega)]
    exact hI.z i hi
  · exact hI.fr.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [h1, h2, h3, h4, ite_false]

/-- The facts of key expansion's precondition on this target (the shared
contract's, `Spec.Cast5.expandKeyContract`, with the table `VG_CAST5_S5678`):
the arguments (`key`, `key_len`, `schedule`, `scratch`) on the stack. -/
structure KPre (s : State) : Prop where
  rdEq : s.rd = [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩,
    ⟨(s.syms s5678Sym).setWidth 64, 4096⟩]
  wrEq : s.wr = [⟨(arg s 2).setWidth 64, 128⟩, ⟨(arg s 3).setWidth 64, 256⟩]
  sp : 4 ≤ (s.gpr .esp).toNat
  spfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  fitk : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  fitK : (arg s 2).toNat + 128 ≤ 2 ^ 32
  fitS : (arg s 3).toNat + 256 ≤ 2 ^ 32
  fitT : (s.syms s5678Sym).toNat + 4096 ≤ 2 ^ 32
  held : Held s.mem ((s.syms s5678Sym).setWidth 64) s5678
  dkK : Region.Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dkS : Region.Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dKS : Region.Disjoint ⟨(arg s 2).setWidth 64, 128⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dTK : Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dTS : Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dAK : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dAS : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dRK : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 128⟩
  dRS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 256⟩
  dK : Region.Disjoint ⟨(arg s 2).setWidth 64, 128⟩ (below (s.gpr .esp) 4)
  dS : Region.Disjoint ⟨(arg s 3).setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dT : Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  len : 5 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 16

/-- Key expansion's contract on x86, as its proof states it. -/
def keyX : Contract isa where
  pre s := KPre s
  post s s' := Spec.Cast5.scheduleAt s'.mem ((arg s 2).setWidth 64) =
    Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 4, arg s₁ i = arg s₂ i) ∧ s₁.syms s5678Sym = s₂.syms s5678Sym

/-- The registers key expansion saves. -/
def keySavedL : List (Reg × Nat) := [(.ebx, keySavedOff), (.edi, keySavedOff + 8), (.ebp, keySavedOff + 12)]

theorem keySaved_eq : keySaved = keySavedL ++ [(.esi, keySavedOff + 4)] := rfl
theorem keyRestore_eq : keyRestore = Spill.restoreCode .esi keySaved := rfl
theorem keySave_eq : keySave = Spill.saveCode .eax keySaved := rfl
theorem keySaved_fits : Spill.Fits 256 keySaved := by decide

theorem keySaved_contains {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) :
    ∀ p ∈ keySaved, Region.Contains (slotR S 64 16) (addr S p.2) 4 := by
  intro p hp
  simp only [keySaved, keySavedOff, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
  · rw [addr_off hfit _ (by decide)]; exact Offset.contains _ (by decide) (by decide) (by decide)

theorem keySaved_in {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) :
    ∀ p ∈ keySaved, Region.Contains ⟨S.setWidth 64, 256⟩ (addr S p.2) 4 := by
  intro p hp
  simp only [keySaved, keySavedOff, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
  · rw [addr_off hfit _ (by decide)]; exact Offset.contains_base _ (by decide) (by decide)

theorem argK_in {s : State} (h : KPre s) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  have hA : InRegions (s.rd ++ s.wr) (argAddr s 0) 16 := by
    rw [h.rdEq]; exact ⟨_, by simp, Region.contains_self _ _⟩
  have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by have := h.spfit; omega)
  rw [e0] at hA
  rw [addr_eq (by have := h.spfit; omega), ← Offset.add_add]
  exact CallLay.inRegions_sub hA (by omega) (by decide)

theorem one32 : (1 : BitVec 32) = BitVec.ofNat 32 1 := rfl

theorem addr_shift (x : BitVec 32) (a : Nat) : addr (x + BitVec.ofNat 32 a) 0 = addr x a :=
  congrArg (BitVec.setWidth 64) (BitVec.add_zero _)

theorem key_correct (s : State) (h : KPre s) :
    WP isa expandKey s fun s' => abiPreserved s s' ∧ keyX.post s s' := by
  obtain ⟨kk, hkk⟩ : ∃ x, arg s 0 = x := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ x, arg s 1 = x := ⟨_, rfl⟩
  obtain ⟨K32, hK32⟩ : ∃ x, arg s 2 = x := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ x, arg s 3 = x := ⟨_, rfl⟩
  have fitS : S.toNat + 256 ≤ 2 ^ 32 := hS ▸ h.fitS
  have fitK : K32.toNat + 128 ≤ 2 ^ 32 := hK32 ▸ h.fitK
  have fitk : kk.toNat + L.toNat ≤ 2 ^ 32 := hkk ▸ hL ▸ h.fitk
  have hlen : 5 ≤ L.toNat ∧ L.toNat ≤ 16 := hL ▸ h.len
  have wS : InRegions s.wr (S.setWidth 64) 256 := by rw [h.wrEq, hS]; exact ⟨_, by simp, Region.contains_self _ _⟩
  have wK : InRegions s.wr (K32.setWidth 64) 128 := by
    rw [h.wrEq, hK32]; exact ⟨_, by simp, Region.contains_self _ _⟩
  have rk : InRegions (s.rd ++ s.wr) (kk.setWidth 64) L.toNat := by
    rw [h.rdEq, hkk, hL]; exact ⟨_, by simp, Region.contains_self _ _⟩
  have a0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := argK_in h (i := 0) (by decide)
  have a1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := argK_in h (i := 1) (by decide)
  have a2 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := argK_in h (i := 2) (by decide)
  have a3 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4 := argK_in h (i := 3) (by decide)
  have v3 : s.mem.readW (addr (s.gpr .esp) 16) 32 = S := hS
  -- The saved registers' memory.
  let g := (s.setReg .eax S).gpr
  let SM := Spill.saveMem s.mem (addr S) g keySaved
  have fSM : Frame [⟨S.setWidth 64, 256⟩] s.mem SM :=
    Spill.saveMem_frame List.mem_cons_self (addr S) g keySaved s.mem (keySaved_in fitS)
  have argSM (i : Nat) (hi : i < 3) : SM.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := by
    refine Spill.saveMem_readW_of_sep _ _ (by decide) keySaved s.mem fun p hp => ?_
    refine Region.Disjoint.sep (h.dAS) ?_ ?_
    · have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by have := h.spfit; omega)
      rw [addr_eq (by have := h.spfit; omega), e0, ← Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [hS]; exact keySaved_in fitS p hp
  have sk : SM.readW (addr (s.gpr .esp) 4) 32 = kk := (argSM 0 (by decide)).trans hkk
  have sl : SM.readW (addr (s.gpr .esp) 8) 32 = L := (argSM 1 (by decide)).trans hL
  have sK : SM.readW (addr (s.gpr .esp) 12) 32 = K32 := (argSM 2 (by decide)).trans hK32
  have w16 := slot_wr (s := s) fitS wS (d := xOff) (n := 4) (by decide)
  have w20 := slot_wr (s := s) fitS wS (d := xOff + 4) (n := 4) (by decide)
  have w24 := slot_wr (s := s) fitS wS (d := xOff + 8) (n := 4) (by decide)
  have w28 := slot_wr (s := s) fitS wS (d := xOff + 12) (n := 4) (by decide)
  unfold expandKey
  rw [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.mov .eax (.mem (at_ .esp 16))]) s fun s₁ => s₁ = s.setReg .eax S := by
    crun [a3, v3]
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [keySave_eq]
  refine Spill.save_ok keySaved (fun p hp => ?_) fun s₂ u₂ => ?_
  · rw [wr_setReg, gpr_setReg_self]
    exact slot_wr fitS wS (d := p.2) (n := 4) (by have := keySaved_fits.1 p hp; omega)
  have g₂ : s₂.gpr = g := u₂.gpr
  have m₂ : s₂.mem = SM := by rw [u₂.mem]; rfl
  have rd₂ : s₂.rd = s.rd := u₂.rd
  have wr₂ : s₂.wr = s.wr := u₂.wr
  have sy₂ : s₂.syms = s.syms := u₂.syms
  have hge : g .eax = S := gpr_setReg_self _ _ _
  have hgsp : g .esp = s.gpr .esp := gpr_setReg_of_ne _ _ (by decide)
  have hsetup : WP isa (.block keySetup) s₂ fun s₃ => s₃.mem = zeroMem SM S ∧ s₃.gpr .esi = S ∧
      s₃.gpr .edi = kk ∧ s₃.gpr .ebx = L ∧ s₃.gpr .edx = K32 ∧ s₃.gpr .eax = S + BitVec.ofNat 32 16 ∧
      s₃.gpr .esp = s.gpr .esp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧ s₃.syms = s.syms := by
    unfold keySetup
    crun [g₂, m₂, rd₂, wr₂, sy₂, hge, hgsp, a0, a1, a2, sk, sl, sK, w16, w20, w24, w28]
    exact ⟨rfl, rfl⟩
  refine WP.mono hsetup fun s₃ ⟨m₃, si₃, di₃, bx₃, dx₃, ax₃, sp₃, rd₃, wr₃, sy₃⟩ => ?_
  have dkS64 : Region.Disjoint ⟨kk.setWidth 64, L.toNat⟩ ⟨S.setWidth 64, 64⟩ := by
    have := h.dkS; rw [hkk, hL, hS] at this; exact this.sub_right (Region.sub_prefix (by decide))
  have hkb (j : Nat) (hj : j < L.toNat) (m : Mem) (hf : Frame [⟨S.setWidth 64, 64⟩] SM m) :
      m (kk.setWidth 64 + BitVec.ofNat 64 j) = SM (kk.setWidth 64 + BitVec.ofNat 64 j) := by
    refine hf.bytes (R := ⟨kk.setWidth 64, L.toNat⟩) (fun r hr => ?_) (by show L.toNat ≤ 2 ^ 64; omega) hj
    rw [List.mem_singleton] at hr; rw [hr]; exact dkS64
  refine WP.seq (wp_countdown (cnt := .ebx) (N := L.toNat) (by omega) (by omega)
    (fun j u => CInv SM (kk.setWidth 64) (S.setWidth 64) j u.mem ∧ u.gpr .edi = kk + BitVec.ofNat 32 j ∧
      u.gpr .eax = S + BitVec.ofNat 32 (16 + j) ∧
      (∀ r, r ∉ [Reg.eax, .edi, .ebx, .ecx] → u.gpr r = s₃.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms)
    (fun j hj u ⟨cu, du, au, gu, rdu, wru, syu⟩ _ => WP.mono (copyStep_ok u (by omega) cu du au
      (by rw [addr_shift]; exact addr_eq (by omega))
      (by rw [addr_shift]; exact addr_eq (by omega))
      (by rw [rdu, wru]; exact CallLay.inRegions_sub rk (by omega) (by omega))
      (by rw [wru]; exact CallLay.inRegions_sub wS (by omega) (by decide))
      (hkb j hj u.mem cu.fr))
      fun v ⟨cv, dv, av, sv, zv, gv, rdv, wrv, syv⟩ => ⟨⟨cv, by rw [dv, one32, add_ofNat_add32 _ j 1], by
        rw [av, one32, add_ofNat_add32 _ (16 + j) 1, Nat.add_assoc], fun r hr => ?keepStep, rdv.trans rdu, wrv.trans wru,
        syv.trans syu⟩, sv, zv⟩)
    (fun u hu => ?rest)
    ⟨by rw [m₃]; exact zeroMem_cinv SM fitS _, by rw [di₃]; exact (BitVec.add_zero _).symm, by rw [ax₃],
      fun _ _ => rfl, rd₃, wr₃, sy₃⟩ (by rw [bx₃, ofNat_toNat32]))
  case keepStep =>
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [gv r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, gu r hr]
  case rest =>
    obtain ⟨cu, -, -, gu, rdu, wru, syu⟩ := hu
    have hsi_u : u.gpr .esi = S := (gu .esi (by decide)).trans si₃
    have hdx_u : u.gpr .edx = K32 := (gu .edx (by decide)).trans dx₃
    have hsp_u : u.gpr .esp = s.gpr .esp := (gu .esp (by decide)).trans sp₃
    refine WP.seq (WP.mono (show WP isa (.block [.mov .edi (.reg .edx), .mov .ebx (imm 2)]) u fun v =>
        v.gpr .edi = K32 ∧ v.gpr .ebx = BitVec.ofNat 32 2 ∧ v.mem = u.mem ∧
          (∀ r, r ≠ .edi → r ≠ .ebx → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms by
      crun [hdx_u]
      exact fun r h1 h2 => by simp only [h1, h2, ite_false]) fun u1 ⟨di1, bx1, m1, g1, rd1, wr1, sy1⟩ => ?_)
    have si1 : u1.gpr .esi = S := (g1 .esi (by decide) (by decide)).trans hsi_u
    have sp1 : u1.gpr .esp = s.gpr .esp := (g1 .esp (by decide) (by decide)).trans hsp_u
    have rd1' : u1.rd = s.rd := rd1.trans rdu
    have wr1' : u1.wr = s.wr := wr1.trans wru
    have sy1' : u1.syms = s.syms := sy1.trans syu
    -- The memory so far: only the working space written.
    have fU : Frame [⟨S.setWidth 64, 256⟩] s.mem u1.mem := by
      rw [m1]
      exact fSM.trans (cu.fr.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩)
    have dSK : Region.Disjoint ⟨K32.setWidth 64, 128⟩ ⟨S.setWidth 64, 256⟩ := by rw [← hK32, ← hS]; exact h.dKS
    have dTS : Region.Disjoint ⟨(s.syms s5678Sym).setWidth 64, 4096⟩ ⟨S.setWidth 64, 256⟩ := by
      rw [← hS]; exact h.dTS
    -- The arrays after the copy.
    let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem (kk.setWidth 64) L.toNat).getD j 0,
      fun j => u1.mem (S.setWidth 64 + BitVec.ofNat 64 (32 + j))⟩
    have xz0 : HoldsXZ u1.mem (S.setWidth 64) st0 := by
      intro a i hi
      cases a with
      | x =>
        rw [show off .x + i = 16 + i from rfl, m1, cu.x i hi]
        show _ = (Spec.Cast5.bytesAt s.mem (kk.setWidth 64) L.toNat).getD i 0
        rw [bytesAt_getD]
        split
        · rw [fSM.bytes (R := ⟨kk.setWidth 64, L.toNat⟩) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; rw [← hkk, ← hL, ← hS]; exact h.dkS)
            (by show L.toNat ≤ 2 ^ 64; omega) (by assumption)]
        · rfl
      | z => rfl
    have held0 : Held u1.mem ((s.syms s5678Sym).setWidth 64) s5678 := by
      intro i hi
      rw [s5678_length] at hi
      rw [fU.readW (r := ⟨(s.syms s5678Sym).setWidth 64, 4096⟩)
        (Offset.contains_base _ (by omega) (by have := h.fitT; omega))
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dTS) (by decide)]
      exact h.held i (by rw [s5678_length]; exact hi)
    have ks0 : KS u1.mem S (K32.setWidth 64) u1 st0 [] := by
      refine ⟨si1, fitS, by rw [wr1']; exact wS, ⟨xz0, fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _⟩,
        Nat.zero_le _, by rw [wr1']; exact wK, dSK, by rw [sp1]; exact h.sp, by rw [sp1, ← hS]; exact h.dS,
        by rw [sp1, ← hK32]; exact h.dK, by rw [sy1']; exact h.fitT,
        by rw [rd1', wr1', sy1', h.rdEq]; exact ⟨_, by simp, Region.contains_self _ _⟩, ?_, by rw [sy1']; exact held0⟩
      intro r hr
      rw [sy1']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dTS
      · rw [← hK32]; exact h.dTK
      · rw [sp1]; exact h.dT
    refine WP.seq (wp_countdown (cnt := .ebx) (N := 2) (by decide) (by decide)
      (fun hh v => KS u1.mem S (K32.setWidth 64) v (halves st0 hh).1 (halves st0 hh).2 ∧
        v.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh) ∧ v.syms = s.syms ∧ Keep keyRegs u1 v)
      (fun hh hh2 v ⟨kv, dv, syv, kpv⟩ _ => WP.mono (half_ok kv rfl fitK dv (halves_length st0 hh) hh2)
        fun w ⟨kw, dw, sw, zw, syw, kpw⟩ => ⟨⟨kw, dw, syw.trans syv, kpv.trans kpw⟩, sw, zw⟩)
      (fun v hv => ?fin)
      ⟨ks0, by rw [di1]; exact (BitVec.add_zero _).symm, sy1', Keep.refl _ _⟩ bx1)
    case fin =>
      obtain ⟨kv, -, syv, kpv⟩ := hv
      have vsi : v.gpr .esi = S := (kpv.gpr .esi (by decide)).trans si1
      have vsp : v.gpr .esp = s.gpr .esp := (kpv.gpr .esp (by decide)).trans sp1
      have vrd : v.rd = s.rd := kpv.rd.trans rd1'
      have vwr : v.wr = s.wr := kpv.wr.trans wr1'
      -- The saved registers.
      have hs0 : Spill.Saved SM (addr S) g keySaved := Spill.saveMem_saved_addr s.mem g keySaved_fits fitS
      have d64 : Region.Disjoint (slotR S 64 16) ⟨S.setWidth 64, 64⟩ :=
        Offset.disjoint_base _ (by decide) (by decide)
      have hs1 : Spill.Saved u1.mem (addr S) g keySaved := by
        rw [m1]
        exact hs0.of_frame cu.fr (keySaved_contains fitS) fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact d64
      have hs2 : Spill.Saved v.mem (addr S) g keySaved := by
        refine hs1.of_frame kv.mem.fr (keySaved_contains fitS) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact d64
        · exact (dSK.symm).sub_left (slot_sub S (by decide))
        · rw [vsp, ← hS]; exact h.dS.sub_left (by rw [hS]; exact slot_sub S (by decide))
      rw [keyRestore_eq, keySaved_eq, ← List.append_nil (Spill.restoreCode _ _)]
      refine Spill.restoreBase_ok keySavedL (by decide) (fun p hp => ?_) (by rw [vsi, ← keySaved_eq]; exact hs2)
        fun s' hr => WP.block_nil ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
      · rw [vsi, vrd, vwr]
        rw [← keySaved_eq] at hp
        exact slot_rd fitS wS (d := p.2) (n := 4) (by have := keySaved_fits.1 p hp; omega)
      · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl
        · exact (hr.gpr (.ebx, keySavedOff) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.esi, keySavedOff + 4) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.edi, keySavedOff + 8) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.gpr (.ebp, keySavedOff + 12) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
        · exact (hr.other .esp (by decide)).trans vsp
      · have dR : ∀ r ∈ ([⟨S.setWidth 64, 64⟩, ⟨K32.setWidth 64, 128⟩, below (v.gpr .esp) 4] : List Region),
            Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r := by
          intro r hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl | rfl
          · exact (show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨S.setWidth 64, 256⟩ by
              rw [← hS]; exact h.dRS).sub_right (Region.sub_prefix (by decide))
          · rw [← hK32]; exact h.dRK
          · rw [vsp, below, Taint.sub_setWidth h.sp]
            exact Offset.base_disjoint_below _ (by decide)
        rw [hr.mem, kv.mem.fr.readW (Region.contains_self _ _) dR (by decide),
          fU.readW (Region.contains_self _ _) (fun r hr' => by
            rw [List.mem_singleton] at hr'; subst hr'; rw [← hS]; exact h.dRS) (by decide)]
      · show Spec.Cast5.scheduleAt s'.mem _ = _
        rw [hr.mem, hK32, hkk, hL, scheduleAt_keys kv.mem.keys (halves_length st0 2),
          Proof.Cast5.expandKey_eq _ st0.z, halves_two]

end VG.Proof.Cast5.X86
