import VerifiedGarbage.Proof.Cast5.X86_64.KeyHalf
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# CAST5 key expansion on x86-64

`expandKey` pads the key with zeros into `x` (§2.5), then runs both halves of
§2.4 (`expandKey_ok`).
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly sx_ofNat wp_countdown)

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_byte (m : Mem) (c : Addr) {d e : Nat} (hd : d + 8 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (BitVec.setWidth 64 (0#32))) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 8 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) (key : Addr) (hw : InRegions s.wr (s.gpr .rcx) 64) :
    WP isa (.block [.mov32 .rax (imm 0), .store (at_ .rcx xOff) .rax, .store (at_ .rcx (xOff + 8)) .rax,
      .mov .rax (.reg .rcx), .alu .add .rax (imm xOff)]) s fun u =>
      CInv s.mem key (s.gpr .rcx) 0 u.mem ∧ u.gpr .rax = s.gpr .rcx + BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .rax → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms := by
  have h16 := scr_w hw (d := 16) (n := 8) (by decide)
  have h24 := scr_w hw (d := 24) (n := 8) (by decide)
  unfold xOff
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, sx_ofNat (show 16 < 2 ^ 31 by decide), h16, h24,
    Nat.reduceAdd]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, fun r hr => ?_, rfl⟩
  · rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, zero_byte _ _ (by decide) (by omega),
      zero_byte _ _ (by decide) (by omega)]
    split <;> split <;> first | rfl | omega
  · rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, zero_byte _ _ (by decide) (by omega),
      zero_byte _ _ (by decide) (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · simp only [hr, ite_false]

theorem copyStep_ok (u : State) {m0 : Mem} {key c : Addr} {j : Nat} (hj : j < 16) (hI : CInv m0 key c j u.mem)
    (hdi : u.gpr .rdi = key + BitVec.ofNat 64 j) (hax : u.gpr .rax = c + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (key + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (c + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (key + BitVec.ofNat 64 j) = m0 (key + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 key c (j + 1) v.mem ∧ v.gpr .rdi = key + BitVec.ofNat 64 (j + 1) ∧
      v.gpr .rax = c + BitVec.ofNat 64 (16 + (j + 1)) ∧ v.gpr .rsi = u.gpr .rsi - 1 ∧
      v.zf = some (u.gpr .rsi - 1 == 0) ∧ (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .r9 → v.gpr r = u.gpr r) ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms := by
  unfold copyStep
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, sx_ofNat (show 1 < 2 ^ 31 by decide), hdi, hax, hr, hw, hk,
    Proof.Cast5.add_ofNat_add]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, by rw [Nat.add_assoc], rfl, rfl, fun r h1 h2 h3 h4 => ?_, rfl⟩
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega) (by omega)]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨Nat.le_refl _, by omega⟩, ite_eq_left (by omega), Nat.sub_self]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [ite_eq_right (by omega), hI.x i hi]
      by_cases hl : i < j
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega) (by omega), ite_eq_right (by omega)]
    exact hI.z i hi
  · exact hI.fr.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [h1, h2, h3, h4, ite_false]

/-- The facts of key expansion's precondition on this target (the shared
contract's, `Spec.Cast5.expandKeyContract`, with the table `VG_CAST5_S5678`). -/
structure KPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.syms s5678Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .rdx, 128⟩, ⟨s.gpr .rcx, 256⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s5678Sym + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0
  fitT : (s.syms s5678Sym).toNat + 4096 ≤ 2 ^ 64
  dTK : Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ ⟨s.gpr .rdx, 128⟩
  dTS : Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ ⟨s.gpr .rcx, 256⟩
  dkK : Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .rdx, 128⟩
  dkS : Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .rcx, 256⟩
  dKS : Region.Disjoint ⟨s.gpr .rdx, 128⟩ ⟨s.gpr .rcx, 256⟩
  dspk : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dspK : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 128⟩
  dspS : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 256⟩
  fk : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  fK : (s.gpr .rdx).toNat + 128 ≤ 2 ^ 64
  fS : (s.gpr .rcx).toNat + 256 ≤ 2 ^ 64
  len : 5 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 16

/-- The registers key expansion writes. -/
def keyAll : List Reg := [.rax, .r9, .r10, .r11, .rdx, .rsi, .rdi]

theorem expandKey_ok (s : State) (h : KPre s) :
    WP isa expandKey s fun u =>
      Spec.Cast5.scheduleAt u.mem (s.gpr .rdx) =
        Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) ∧
      Keep keyAll s u ∧ Frame [⟨s.gpr .rdx, 128⟩, ⟨s.gpr .rcx, 256⟩] s.mem u.mem := by
  obtain ⟨n, hn⟩ : ∃ n, (s.gpr .rsi).toNat = n := ⟨_, rfl⟩
  obtain ⟨key, hkey⟩ : ∃ key, s.gpr .rdi = key := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, s.gpr .rcx = c := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .rdx = K := ⟨_, rfl⟩
  have hl := h.len
  rw [hn] at hl
  have hwS : InRegions s.wr c 256 := by
    rw [h.wr, hc]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  have hwK : InRegions s.wr K 128 := by
    rw [h.wr, hK]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
  have hw64 : InRegions s.wr c 64 := by
    have := CallLay.inRegions_sub hwS (off := 0) (l := 64) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have hrK : InRegions (s.rd ++ s.wr) key n := by
    rw [h.rd, hkey, hn]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
  have dkc : Region.Disjoint ⟨key, n⟩ ⟨c, 64⟩ := by
    have := h.dkS; rw [hkey, hn, hc] at this; exact this.sub_right (Region.sub_prefix (by decide))
  unfold expandKey
  refine WP.seq (WP.mono (zero_ok s key (by rw [hc]; exact hw64)) fun u0 ⟨c0, ax0, g0, rd0, wr0, sy0⟩ => ?_)
  rw [hc] at c0 ax0
  have hkb (j : Nat) (hj : j < n) (m : Mem) (hf : Frame [⟨c, 64⟩] s.mem m) :
      m (key + BitVec.ofNat 64 j) = s.mem (key + BitVec.ofNat 64 j) := by
    refine hf.bytes (R := ⟨key, n⟩) (fun r hr => ?_) (by show n ≤ 2 ^ 64; omega) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact dkc
  have hsi0 : u0.gpr .rsi = BitVec.ofNat 64 n := by
    rw [g0 _ (by decide), ← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (wp_countdown (cnt := .rsi) (N := n) (by omega) (by omega)
    (fun j u => CInv s.mem key c j u.mem ∧ u.gpr .rdi = key + BitVec.ofNat 64 j ∧
      u.gpr .rax = c + BitVec.ofNat 64 (16 + j) ∧ (∀ r, r ∉ [Reg.rax, .rdi, .rsi, .r9] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms)
    (fun j hj u ⟨cu, du, au, gu, rdu, wru, syu⟩ _ => WP.mono (copyStep_ok u (by omega) cu du au
      (by rw [rdu, wru]; exact CallLay.inRegions_sub hrK (by omega) (by omega))
      (by rw [wru]; exact scr_w hw64 (by omega))
      (hkb j hj u.mem cu.fr))
      fun v ⟨cv, dv, av, sv, zv, gv, rdv, wrv, syv⟩ => ⟨⟨cv, dv, av, fun r hr => ?keepStep, rdv.trans rdu,
        wrv.trans wru, syv.trans syu⟩, sv, zv⟩)
    (fun u hu => ?rest) ⟨c0, by rw [g0 _ (by decide), hkey, BitVec.add_zero], by rw [ax0], fun r hr => ?keep0, rd0,
      wr0, sy0⟩ hsi0)
  case keepStep =>
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [gv r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, gu r hr]
  case keep0 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g0 r hr.1
  case rest =>
    obtain ⟨cu, -, -, gu, rdu, wru, syu⟩ := hu
    refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rsi (imm 2)]) u fun v =>
        v.gpr .rsi = BitVec.ofNat 64 2 ∧ v.mem = u.mem ∧ (∀ r, r ≠ .rsi → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
          v.wr = u.wr ∧ v.syms = u.syms by
      xrun [imm]
      exact ⟨fun r hr => ite_eq_right hr, rfl⟩) fun u1 ⟨si1, m1, g1, rd1, wr1, sy1⟩ => ?_)
    have g1s (r : Reg) (hr : r ∉ [Reg.rax, .rdi, .rsi, .r9]) : u1.gpr r = s.gpr r := by
      rw [g1 r (fun e => hr (by rw [e]; simp)), gu r hr]
    let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem key n).getD j 0,
      fun j => s.mem (c + BitVec.ofNat 64 (32 + j))⟩
    have hT : s.syms s5678Sym = u1.syms s5678Sym := by rw [sy1, syu]
    have xz0 : HoldsXZ u1.mem c st0 := by
      intro a i hi
      rw [m1]
      cases a with
      | x => rw [show off .x + i = 16 + i from rfl, cu.x i hi]; exact (bytesAt_getD _ _ _ _).symm
      | z => exact cu.z i hi
    have fr0 : Frame [⟨c, 64⟩, ⟨K, 128⟩] s.mem u1.mem := by
      rw [m1]
      refine cu.fr.mono fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hr]; exact List.mem_cons_self
    have tab0 : Readable u1 (u1.syms s5678Sym) := by
      unfold Readable; rw [rd1, rdu, wr1, wru, ← hT, h.rd]
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
    have held0 : Held s.mem (u1.syms s5678Sym) s5678 := by
      rw [← hT]; intro i hi
      rw [show s5678.length = 512 from table_length _ _ _ _] at hi
      exact h.held i hi
    have dT0 : ∀ r ∈ ([⟨c, 64⟩, ⟨K, 128⟩] : List Region), Region.Disjoint ⟨u1.syms s5678Sym, 4096⟩ r := by
      intro r hr
      rw [← hT]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := h.dTS; rw [hc] at this; exact this.sub_right (Region.sub_prefix (by decide))
      · have := h.dTK; rw [hK] at this; exact this
    have dKS0 : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩ := by
      have := h.dKS; rw [hK, hc] at this; exact this.sub_right (Region.sub_prefix (by decide))
    have ks0 : KS s.mem c K u1 st0 [] :=
      ⟨by rw [g1s _ (by decide), hc], ⟨xz0, fun i hi => absurd hi (Nat.not_lt_zero _), fr0⟩, Nat.zero_le _,
        by rw [wr1, wru]; exact hw64, by rw [wr1, wru]; exact hwK, dKS0, tab0, held0, dT0⟩
    refine wp_countdown (cnt := .rsi) (N := 2) (by decide) (by decide)
      (fun hh v => KS s.mem c K v (halves st0 hh).1 (halves st0 hh).2 ∧
        v.gpr .rdx = K + BitVec.ofNat 64 (64 * hh) ∧ v.syms = s.syms ∧ Keep keyRegs u1 v)
      (fun hh hh2 v ⟨kv, dv, syv, kpv⟩ _ => WP.mono (half_ok kv dv (halves_length st0 hh) hh2)
        fun w ⟨kw, dw, sw, zw, syw, kpw⟩ => ⟨⟨kw, dw, syw.trans syv, keep_same kpv kpw⟩, sw, zw⟩)
      (fun v ⟨kv, _, _, kpv⟩ => ?_)
      ⟨ks0, by rw [g1s _ (by decide), hK, Nat.mul_zero, BitVec.add_zero], by rw [sy1, syu],
        Keep.refl _ _⟩ si1
    rw [hK, hkey, hn, hc]
    refine ⟨?_, ⟨fun r hr => ?_, by rw [kpv.2.1, rd1, rdu], by rw [kpv.2.2, wr1, wru]⟩, ?_⟩
    · rw [scheduleAt_keys kv.mem.keys (halves_length st0 2), Proof.Cast5.expandKey_eq _ st0.z]
      rfl
    · simp only [keyAll, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [kpv.1 r (by simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1⟩)]
      exact g1s r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨hr.1, hr.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.1⟩)
    · refine kv.mem.fr.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩

end VG.Proof.Cast5.X86_64
