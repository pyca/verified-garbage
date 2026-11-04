module
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
public import VerifiedGarbage.Proof.MdHashTable.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Syms

import VerifiedGarbage.Proof.RsaPss.X86_64.CtHash
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# RSASSA-PSS on x86-64: compressing every block, selecting the last

`compLoop` compresses each of the `nbm` blocks of `Y` into the hash value at
`scratch + oSt` by calling the compression function, and copies the hash
value to `scratch + oSel` under the mask of the block being the last of the
padded message (`compLoop_ok`): afterwards that is the hash value of the
first `fb + 1` blocks.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn load64_eq store64_eq)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Proof.MdStream.X86_64 (compressK)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {H : Hash} (hH : HashOK H)

/-- The return address of a call from the frame changes neither the frame
nor our working space. -/
theorem Rep.callEntry {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) : Rep u.callEntry.mem F S V W :=
  R.frame (rgs := []) L.geo (by simp) (by
    rw [State.callEntry_mem, L.rsp]
    exact Frame.writeW (Frame.refl _ _) (by simp [regs]) _ (below_call _ (n := 16) (by decide) (by decide)))
    |> fun R' => (congrArg (fun V' => Rep u.callEntry.mem F S V' W) (funext fun o => by
      simp only [inR, List.not_mem_nil, false_and, exists_false, ite_false])).mp R'

/-- The bytes of the hash value at `scratch + o` in two memories agree. -/
theorem stateAt_rep {m m' : Mem} {F S : Addr} {V V' : Nat → Byte} {W W' : Nat → BitVec 64}
    (R : Rep m F S V W) (R' : Rep m' F S V' W') {o : Nat} (ho : o + H.P.N ≤ oRsa)
    (h : ∀ i < H.P.N, V' (o + i) = V (o + i)) : hH.md.stateAt m' (off S o) = hH.md.stateAt m (off S o) :=
  hH.md.stateAt_congr fun i hi => by
    rw [show off S o + BitVec.ofNat 64 i = off S (o + i) from off_off S o i, R'.scr _ (by omega_using [ho, hi]),
      R.scr _ (by omega_using [ho, hi]), h i hi]

theorem ofNat_add_S (S : Addr) (a c : Nat) : BitVec.ofNat 64 a + S + BitVec.ofNat 64 c = off S (c + a) := by
  rw [BitVec.add_comm (BitVec.ofNat 64 a) S, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

include hH in
/-- The arguments of the compression function, for block `b`. -/
theorem compArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {b : Nat} (hb : b ≤ 2048) (hW : W 29 = BitVec.ofNat 64 b) :
    WP isa (.block (compArgs H)) u fun u' => u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = off S (oY + H.P.B * b) ∧
      u'.gpr .rdx = 1 ∧ u'.gpr .rcx = S ∧ u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] u u' := by
  obtain ⟨hpow, hlg1, hlg2⟩ := lgB_spec hH
  have hB := hH.B_le
  have hs := L.slot
  simp only [Bignum.word] at hs
  have e29 : u.mem.readW (off F sB) 64 = BitVec.ofNat 64 b := by rw [← hW, ← R.fr 29 (by decide)]; rfl
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = off S (oY + H.P.B * b) ∧ u'.gpr .rdx = 1 ∧ u'.gpr .rcx = S ∧ u'.mem = u.mem) ?_ rfl)
    fun u' ⟨⟨h1, h2, h3, h4, h5⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, hk⟩
  xrun [compArgs, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide),
    L.ld (d := sB) (by decide), hs, e29, VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oY < 2 ^ 31 by decide),
    ror_mul (x := b) (k := lgB H) (B := H.P.B) (by omega_using [hlg1]) (by omega_using [hlg2]) hpow (show b * H.P.B < 2 ^ 64 by
      have := Nat.mul_le_mul hb hB; omega_using [this]),
    show 1 ≤ 64 - lgB H ∧ 64 - lgB H ≤ 63 from ⟨by omega_using [hlg2], by omega_using [hlg1]⟩, show ¬ 64 - lgB H = 1 by omega_using [hlg2],
    ofNat_add_S, Nat.mul_comm b H.P.B]

include hH in
/-- Compressing block `b` of `Y` into the hash value at `scratch + oSt`. -/
theorem compCall_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {b : Nat} (hbB : H.P.B * b + H.P.B ≤ 2048) (hW : W 29 = BitVec.ofNat 64 b)
    {dn : String} {f : MdFns} (hT : HT H dn f W u.syms) :
    WP isa (.seq (.block (compArgs H)) (scall sCmpH f.comp)) u fun u' =>
      Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      Rep u'.mem F S (fun o => if inR [(oSt, H.P.N), (0, H.P.so)] o then u'.mem (off S o) else V o) W ∧
      hH.md.stateAt u'.mem (off S oSt) =
        hH.md.compress (hH.md.stateAt u.mem (off S oSt)) (hH.md.parse fun k => V (oY + H.P.B * b + k)) := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hN := hH.N_le
  have hso := hH.hso
  have hbb : b ≤ H.P.B * b := Nat.le_mul_of_pos_left b hB0
  refine WP.seq (X86_64.WP.mono_syms (compArgs_ok hH L R (b := b) (by omega_using [hbB, hbb]) hW)
    fun v₀ ⟨hdi₀, hsi₀, hdx₀, hcx₀, hm₀, hk₀⟩ y₀ => ?_)
  have Lv₀ : Lay v₀ F S := L.congr (hk₀.gpr (by decide)) hk₀.2.2 (by rw [hm₀])
  refine scall_ok Lv₀ (hm₀ ▸ R) (k := 9) rfl (by decide) (by decide) (by rw [y₀]; exact hT.wc) (by rw [y₀]; exact hT.fc)
    fun v k₁ hm₁ _ => ?_
  have hk : Keep [.rdi, .rsi, .rdx, .rcx, .r11] u v := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₁.gpr (by simp [hr.2.2.2.2]), hk₀.gpr (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1])],
    k₁.2.1.trans hk₀.2.1, k₁.2.2.trans hk₀.2.2⟩
  have hm : v.mem = u.mem := hm₁.trans hm₀
  have hdi : v.gpr .rdi = _ := (k₁.gpr (by decide)).trans hdi₀
  have hsi : v.gpr .rsi = _ := (k₁.gpr (by decide)).trans hsi₀
  have hdx : v.gpr .rdx = _ := (k₁.gpr (by decide)).trans hdx₀
  have hcx : v.gpr .rcx = _ := (k₁.gpr (by decide)).trans hcx₀
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have cS0 : ∀ {o n : Nat}, o + n ≤ oRsa → Covers [⟨off S o, n⟩] v.wr := fun h => Lv.cov h
  have hS0 : off S 0 = S := BitVec.add_zero S
  refine WP.call (k := compressK hH.md) hH.comp.verified hH.comp.nosp (by rw [hH.comp.depth]; decide)
    (rd := [⟨off S (oY + H.P.B * b), H.P.B * 1⟩]) (wr := [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩]) ?_ ?_ ?_ ?_
  · simp only [compressK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      hdi, hsi, hdx, hcx, Lv.rsp, show (1 : BitVec 64).toNat = 1 from rfl, true_and]
    refine ⟨Offset.disjoint_base S (by unfold oSt; omega_using [hso]) (by unfold oSt; omega_using [hN]),
      Offset.disjoint S (by unfold oY oSt; omega_using [hN]) (by unfold oY; omega_using [hbB]) (by unfold oSt; omega_using [hN]),
      Offset.disjoint_base S (by unfold oY; omega_using [hso]) (by unfold oY; omega_using [hbB]),
      Region.Disjoint.sub_right L.dR8 (Offset.sub_base S (by unfold oSt oRsa; omega_using [hN])),
      Region.Disjoint.sub_right L.dR8 (Region.sub_prefix (by unfold oRsa; omega_using [hso]))⟩
  · have c₁ := cS0 (o := 0) (n := H.P.so) (by unfold oRsa; omega_using [hso])
    rw [hS0] at c₁
    exact Covers.right (Covers.append_left (cS0 (by unfold oY oRsa; omega_using [hbB]))
      (Covers.pair (cS0 (by unfold oSt oRsa; omega_using [hN])) c₁))
  · have c₁ := cS0 (o := 0) (n := H.P.so) (by unfold oRsa; omega_using [hso])
    rw [hS0] at c₁
    exact Covers.pair (cS0 (by unfold oSt oRsa; omega_using [hN])) c₁
  · intro u' hrd hwr hcs hF _ ⟨s₂, hm₂, _, hpost⟩
    simp only [compressK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), hdi, hsi, hdx, hm₂,
      show (1 : BitVec 64).toNat = 1 from rfl, MdStream.Md.compressBlocks_one] at hpost
    rw [hH.comp.depth, Lv.rsp] at hF
    obtain ⟨L', R'⟩ := Lv.after_call Rv (rgs := [(oSt, H.P.N), (0, H.P.so)])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro p (rfl | rfl) <;> simp only [oSt, oRsa] <;> omega_using [hN, hso]) (by simpa [regs, hS0] using frame_ret hF)
      (hcs .rsp (by decide)) hwr
    refine ⟨L', hrd.trans hk.2.1, hwr.trans hk.2.2, fun r hr => (hcs r hr).trans (hk.gpr ?_), R', ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hpost]
    have RE := Rep.callEntry Lv Rv
    rw [stateAt_rep hH Rv RE (o := oSt) (by unfold oSt oRsa; omega_using [hN]) (fun _ _ => rfl), hm]
    refine congrArg (hH.md.compress _) (hH.md.parse_congr fun k hk => ?_)
    rw [show off S (oY + H.P.B * b) + BitVec.ofNat 64 k = off S (oY + H.P.B * b + k) from off_off _ _ _,
      RE.scr _ (by unfold oY oRsa; omega_arith)]

/-! ## The selection -/

/-- The working space after the selection of block `b`: the hash value
copied to `oSel` if `b = fb`. -/
def selV (V : Nat → Byte) (c : Bool) (j : Nat) (o : Nat) : Byte :=
  if oSel ≤ o ∧ o < oSel + j then (if c then V (oSt + (o - oSel)) else V o) else V o

theorem selV_out {V : Nat → Byte} {c : Bool} {j o : Nat} (h : ¬ (oSel ≤ o ∧ o < oSel + j)) :
    selV V c j o = V o := by simp only [selV, h, ite_false]

theorem selV_in {V : Nat → Byte} {c : Bool} {j i : Nat} (h : i < j) :
    selV V c j (oSel + i) = if c then V (oSt + i) else V (oSel + i) := by
  simp only [selV, show oSel ≤ oSel + i ∧ oSel + i < oSel + j from ⟨by omega_using [], by omega_using [h]⟩, ite_true,
    Nat.add_sub_cancel_left, and_self]

structure SI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (c : Bool) (j : Nat)
    (u : State) : Prop where
  L : Lay u F S
  keep : Keep [.rcx, .rax, .r11, .r8, .rdx] u₀ u
  rcx : u.gpr .rcx = S
  r11 : u.gpr .r11 = 0#64 - BitVec.setWidth 64 (BitVec.ofBool c)
  r8 : u.gpr .r8 = BitVec.ofNat 64 j
  R : Rep u.mem F S (selV V c j) W

include hH in
theorem select_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {b fb : Nat} (hb : W 29 = BitVec.ofNat 64 b) (hf : W 30 = BitVec.ofNat 64 fb)
    (hb' : b < 2 ^ 64) (hfb' : fb < 2 ^ 64) :
    WP isa (select H) u fun u' => SI u F S V W (decide (b = fb)) H.P.N u' := by
  have hN := hH.dims.N
  have hs := L.slot
  simp only [Bignum.word] at hs
  have e29 : u.mem.readW (off F sB) 64 = BitVec.ofNat 64 b := by rw [← hb, ← R.fr 29 (by decide)]; rfl
  have e30 : u.mem.readW (off F sFb) 64 = BitVec.ofNat 64 fb := by rw [← hf, ← R.fr 30 (by decide)]; rfl
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax, .r11, .r8, .rdx] (Q := fun v => v.gpr .rcx = S ∧
      v.gpr .r11 = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (b = fb))) ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧
      v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, hm⟩, hk⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sB) (by decide), L.ld (d := sFb) (by decide),
      hs, e29, e30, xor_lt_one hb' hfb']
  refine wp_upto (a := 0) (N := H.P.N) (by omega_using [hN]) (SI u F S V W (decide (b = fb))) ?_ (fun _ h => h)
    ⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), hk, h₁, h₂, h₃,
      hm ▸ (congrArg (fun V' => Rep u.mem F S V' W) (funext fun o => by
        simp only [selV, Nat.add_zero]; split <;> first | omega_arith | rfl)).mpr R⟩
  intro j _ hj w J
  have ea₁ : S + BitVec.ofNat 64 j + BitVec.ofNat 64 oSt = off S (oSt + j) := by
    rw [off_ix, Nat.add_comm]
  have ea₂ : S + BitVec.ofNat 64 j + BitVec.ofNat 64 oSel = off S (oSel + j) := by
    rw [off_ix, Nat.add_comm]
  have l₁ := J.L.sld8 (d := oSt + j) (by unfold oSt oRsa; omega_using [hN, hj])
  have l₂ := J.L.sld8 (d := oSel + j) (by unfold oSel oRsa; omega_using [hN, hj])
  have s₂ := J.L.sst8 (d := oSel + j) (by unfold oSel oRsa; omega_using [hN, hj])
  refine WP.mono (WP.keep [.rax, .rdx, .r8] (Q := fun w' => w'.zf = some (decide (j + 1 = H.P.N)) ∧
      w'.gpr .r8 = BitVec.ofNat 64 (j + 1) ∧
      w'.mem = w.mem.writeW (off S (oSel + j))
        (if decide (b = fb) then w.mem (off S (oSt + j)) else w.mem (off S (oSel + j)))) ?_ rfl)
    fun w' ⟨⟨hz, h8, hm'⟩, hk'⟩ => ⟨hz, ?_⟩
  · xrun [step, List.cons_append, List.nil_append, ea_ix, J.rcx, J.r8, J.r11, ea₁, ea₂, l₁, l₂, s₂, sel_byte,
      ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat (show H.P.N < 2 ^ 31 by omega_using [hN]),
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_using [hN, hj]) (show H.P.N < 2 ^ 64 by omega_using [hN])]
  · rw [J.R.scr _ (by unfold oSt oRsa; omega_using [hN, hj]), J.R.scr _ (by unfold oSel oRsa; omega_using [hN, hj])] at hm'
    have R' := J.R.wb J.L.geo (o := oSel + j) (by unfold oSel oRsa; omega_using [hN, hj])
      (if decide (b = fb) then selV V (decide (b = fb)) j (oSt + j)
        else selV V (decide (b = fb)) j (oSel + j))
    rw [← hm'] at R'
    have R'' : Rep w'.mem F S (selV V (decide (b = fb)) (j + 1)) W := by
      refine (congrArg (fun V' => Rep w'.mem F S V' W) (funext fun o => ?_)).mp R'
      simp only [upd, selV]
      by_cases ho : o = oSel + j
      · subst ho
        have h1 : ¬(oSel ≤ oSt + j ∧ oSt + j < oSel + j) := by unfold oSt oSel; omega_using [hN, hj]
        have h3 : oSel ≤ oSel + j ∧ oSel + j < oSel + (j + 1) := by omega_using []
        simp only [h1, h3, ite_true, ite_false, Nat.add_sub_cancel_left, Nat.lt_irrefl, and_false, true_and]
      · have h' : (oSel ≤ o ∧ o < oSel + (j + 1)) = (oSel ≤ o ∧ o < oSel + j) := by
          apply propext; omega_using [ho]
        simp only [ho, h', ite_false]
    exact ⟨J.L.of_rep J.R R'' (hk'.gpr (by decide)) hk'.2.2, (J.keep.trans hk').mono (by decide),
      (hk'.gpr (by decide)).trans J.rcx, (hk'.gpr (by decide)).trans J.r11, h8, R''⟩

/-! ## The loop -/

/-- Moving the bytes of a hash value. -/
theorem stateAt_mv {m m' : Mem} {F S : Addr} {V V' : Nat → Byte} {W W' : Nat → BitVec 64}
    (R : Rep m F S V W) (R' : Rep m' F S V' W') {o o' : Nat} (ho : o + H.P.N ≤ oRsa) (ho' : o' + H.P.N ≤ oRsa)
    (h : ∀ i < H.P.N, V' (o' + i) = V (o + i)) : hH.md.stateAt m' (off S o') = hH.md.stateAt m (off S o) :=
  hH.reloc m m' (off S o) (off S o') fun i hi => by
    rw [show off S o + BitVec.ofNat 64 i = off S (o + i) from off_off S o i,
      show off S o' + BitVec.ofNat 64 i = off S (o' + i) from off_off S o' i, R'.scr _ (by omega_using [ho', hi]),
      R.scr _ (by omega_using [ho, hi]), h i hi]

theorem nextBlock_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {b nbm : Nat} (hb : W 29 = BitVec.ofNat 64 b) (hn : W 28 = BitVec.ofNat 64 nbm)
    (hb' : b + 1 < 2 ^ 64) (hn' : nbm < 2 ^ 64) :
    WP isa (.block nextBlock) u fun u' => u'.zf = some (decide (b + 1 = nbm)) ∧ Lay u' F S ∧ Keep [.rax, .rdx] u u' ∧
      Rep u'.mem F S V (upd W 29 (BitVec.ofNat 64 (b + 1))) := by
  have e29 : u.mem.readW (off F sB) 64 = BitVec.ofNat 64 b := by rw [← hb, ← R.fr 29 (by decide)]; rfl
  have R' := R.wf L.geo (k := 29) (by decide) (BitVec.ofNat 64 (b + 1))
  rw [show off F (8 * 29) = off F sB from rfl] at R'
  have e28 : (u.mem.writeW (off F sB) (BitVec.ofNat 64 (b + 1))).readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by
    have : upd W 29 (BitVec.ofNat 64 (b + 1)) 28 = W 28 := by simp [upd]
    rw [← hn, ← this, ← R'.fr 28 (by decide)]; rfl
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u' => u'.zf = some (decide (b + 1 = nbm)) ∧
      u'.mem = u.mem.writeW (off F sB) (BitVec.ofNat 64 (b + 1))) ?_ rfl) fun u' ⟨⟨hz, hm⟩, hk⟩ => ?_
  · xrun [nextBlock, ea_sp, L.rsp, L.ld (d := sB) (by decide), L.st (d := sB) (by decide), e29,
      L.ld (d := sNb) (by decide), ofNat_add_lit, e28, ofNat_sub_beq hb' hn']
  · rw [← hm] at R'
    exact ⟨hz, L.congr (hk.gpr (by decide)) hk.2.2 (by
      rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R'.fr 21 (by decide), R.fr 21 (by decide)]; rfl), hk, R'⟩

/-- `Y`'s first `n` bytes. -/
def yList (V : Nat → Byte) (n : Nat) : List Byte := (List.range n).map fun i => V (oY + i)

theorem yList_getD (V : Nat → Byte) {n i : Nat} (hi : i < n) : (yList V n).getD i 0 = V (oY + i) := by
  simp [yList, List.getD_eq_getElem?_getD, hi]

theorem upd_upd {α : Type} (f : Nat → α) (a : Nat) (v w : α) : upd (upd f a v) a w = upd f a w := by
  funext x; simp only [upd]; split <;> rfl

/-- Before block `b`. -/
def CO (t : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (n fb b : Nat) (u : State) : Prop :=
  Lay u F S ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧ u.syms = t.syms ∧
  ∃ V' : Nat → Byte, Rep u.mem F S V' (upd W 29 (BitVec.ofNat 64 b)) ∧
    (∀ o < oRsa, ¬ inR [(oSt, H.P.N), (0, H.P.so), (oSel, H.P.N)] o → V' o = V o) ∧
    hH.md.stateAt u.mem (off S oSt) = hH.md.compressList hH.iv (yList V n) b ∧
    (fb < b → hH.md.stateAt u.mem (off S oSel) = hH.md.compressList hH.iv (yList V n) (fb + 1))

theorem cs_keep {r : Reg} (hr : r ∈ calleeSaved) {rs : List Reg}
    (h : rs.all (fun x => !calleeSaved.contains x) = true) : r ∉ rs := by
  intro h'
  have := List.all_eq_true.mp h r h'
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  exact this hr

include hH in
theorem compLoop_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (hiv : hH.md.stateAt t.mem (off S oSt) = hH.iv) {fb nbm : Nat}
    (hf : W 30 = BitVec.ofNat 64 fb) (hn : W 28 = BitVec.ofNat 64 nbm) (hfb : fb < nbm)
    (hnb : nbm * H.P.B ≤ 2048) {dn : String} {f : MdFns} (hT : HT H dn f W t.syms) :
    WP isa (compLoop f H) t (CO hH t F S V W (nbm * H.P.B) fb nbm) := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hN := hH.N_le
  have hso := hH.hso
  have hnbm : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right nbm hB0) hnb
  refine WP.seq (X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem.writeW (off F sB) (BitVec.ofNat 64 0))
      ?_ rfl) fun u ⟨hm, hk⟩ y0 => ?_)
  · xrun [ea_sp, L.rsp, L.st (d := sB) (by decide)]
    rfl
  have R0 := R.wf L.geo (k := 29) (by decide) (BitVec.ofNat 64 0)
  rw [show off F (8 * 29) = off F sB from rfl, ← hm] at R0
  have L0 : Lay u F S := L.congr (hk.gpr (by decide)) hk.2.2 (by
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R0.fr 21 (by decide), R.fr 21 (by decide)]; rfl)
  have hst0 : hH.md.stateAt u.mem (off S oSt) = hH.md.compressList hH.iv (yList V (nbm * H.P.B)) 0 := by
    rw [stateAt_rep hH R R0 (o := oSt) (by unfold oSt oRsa; omega_using [hN]) (fun _ _ => rfl), hiv]
    exact (MdStream.Md.compressList_zero _ _ _).symm
  refine wp_upto (a := 0) (N := nbm) (by omega_using [hfb]) (CO hH t F S V W (nbm * H.P.B) fb) ?_ (fun _ h => h)
    ⟨L0, hk.2.1, hk.2.2, fun r hr => hk.gpr (cs_keep hr (by decide)), y0, V, R0, fun _ _ _ => rfl, hst0,
      fun h => absurd h (by omega_using [])⟩
  intro b _ hb u ⟨Lu, hrd, hwr, hcs, hsy, V', Ru, hkeep, hst, hsel⟩
  have hbB : H.P.B * b + H.P.B ≤ 2048 := by
    rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left _ hb) (by rw [Nat.mul_comm]; exact hnb)
  refine WP.seq_assoc (WP.seq (X86_64.WP.mono_syms (compCall_ok hH Lu Ru hbB (by simp [upd])
    (by rw [hsy]; exact hT.upd (by decide) _))
    fun v ⟨Lv, hrdv, hwrv, hcsv, Rv, hstv⟩ yv => ?_))
  refine WP.seq (X86_64.WP.mono_syms (select_ok hH Lv Rv (b := b) (fb := fb) (by simp [upd]) (by simp [upd, hf])
    (by omega_using [hnbm, hb]) (by omega_using [hfb, hnbm])) fun w Sw yw => ?_)
  refine X86_64.WP.mono_syms (nextBlock_ok Sw.L Sw.R (b := b) (nbm := nbm) (by simp [upd]) (by simp [upd, hn])
    (by omega_using [hnbm, hb]) (by omega_using [hnbm])) fun u' ⟨hz, Lu', hk', Ru'⟩ yu => ⟨hz, ?_⟩
  rw [upd_upd] at Ru'
  have hY : ∀ i < 2048, V' (oY + i) = V (oY + i) := fun i hi => hkeep _ (by unfold oY oRsa; omega_using [hi]) (by
    simp only [inR_cons, inR_nil, or_false]; unfold oY oSt oSel; omega_using [hN, hso])
  -- The hash value after the block.
  have hst' : hH.md.stateAt u'.mem (off S oSt) = hH.md.compressList hH.iv (yList V (nbm * H.P.B)) (b + 1) := by
    rw [stateAt_rep hH Rv Ru' (o := oSt) (by unfold oSt oRsa; omega_using [hN]) (fun i hi =>
        selV_out (by unfold oSt oSel; omega_using [hN, hi])), hstv, hst, MdStream.Md.compressList_succ]
    refine congrArg (hH.md.compress _) (hH.md.parse_congr fun k hk => ?_)
    rw [Nat.add_assoc, hY _ (by omega_arith),
      yList_getD V (show H.P.B * b + k < nbm * H.P.B by
        have := Nat.mul_le_mul_right H.P.B hb; rw [Nat.succ_mul, Nat.mul_comm b] at this; omega_arith)]
  refine ⟨Lu', hk'.2.1.trans (Sw.keep.2.1.trans (hrdv.trans hrd)), hk'.2.2.trans (Sw.keep.2.2.trans (hwrv.trans hwr)),
    fun r hr => (hk'.gpr (cs_keep hr (by decide))).trans ((Sw.keep.gpr (cs_keep hr (by decide))).trans
      ((hcsv r hr).trans (hcs r hr))), yu.trans (yw.trans (yv.trans hsy)), _, Ru', fun o ho hno => ?_, hst',
    fun hfb' => ?_⟩
  · simp only [inR_cons, inR_nil, or_false, not_or] at hno
    rw [selV_out (by omega_using [hno])]
    simp only [inR_cons, inR_nil, or_false]
    rw [ifn (by omega_using [hno])]
    exact hkeep o ho (by simp only [inR_cons, inR_nil, or_false]; omega_using [hno])
  · by_cases hbf : b = fb
    · subst hbf
      rw [← hst']
      refine stateAt_mv hH Ru' Ru' (by unfold oSt oRsa; omega_using [hN]) (by unfold oSel oRsa; omega_using [hN]) fun i hi => ?_
      rw [selV_in hi, selV_out (by unfold oSt oSel; omega_using [hN, hi])]
      simp
    · rw [← hsel (by omega_using [hfb', hbf])]
      refine stateAt_rep hH Ru Ru' (by unfold oSel oRsa; omega_using [hN]) fun i hi => ?_
      rw [selV_in hi]
      simp only [hbf, decide_false, Bool.false_eq_true, ite_false, inR_cons, inR_nil, or_false]
      rw [ifn (by unfold oSt oSel; omega_using [hN, hso])]

/-! ## The digest -/

include hH in
/-- The digest of the hash value at `scratch + src`, by the table's digest
(`digestK`), to `scratch + oDig`. -/
theorem digestAt_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {src : Nat} (ho : src + H.P.N ≤ oDig) {dn : String} {f : MdFns}
    (hT : HT H dn f W u.syms) (hdk : DigOK H) :
    WP isa (digestAt f src) u fun u' => Lay u' F S ∧ Keep [.rdi, .rsi, .r8, .r9, .r11, .rax] u u' ∧
      Rep u'.mem F S (fun o => if oDig ≤ o ∧ o < oDig + H.P.N then
        (hH.md.digest (hH.md.stateAt u.mem (off S src))).getD (o - oDig) 0 else V o) W := by
  have hN := hH.N_le
  refine WP.seq (X86_64.WP.mono_syms (WP.keep [.rdi, .rsi] (Q := fun v => v.gpr .rdi = off S src ∧
      v.gpr .rsi = off S oDig ∧ v.mem = u.mem) ?_ rfl) fun v₀ ⟨⟨h₁, h₂, hm₀⟩, hk₀⟩ y₀ => ?_)
  · have hs := L.slot
    simp only [Bignum.word] at hs
    xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show src < 2 ^ 31 by unfold oDig at ho; omega_using [ho]),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide)]
  have Lv₀ : Lay v₀ F S := L.congr (hk₀.gpr (by decide)) hk₀.2.2 (by rw [hm₀])
  refine scall_ok Lv₀ (hm₀ ▸ R) (k := 10) rfl (by decide) (by decide) (by rw [y₀]; exact hT.wd)
    (by rw [y₀]; exact hT.fd) fun v k₁ hm₁ _ => ?_
  have hm : v.mem = u.mem := hm₁.trans hm₀
  have hdi : v.gpr .rdi = off S src := (k₁.gpr (by decide)).trans h₁
  have hsi : v.gpr .rsi = off S oDig := (k₁.gpr (by decide)).trans h₂
  have hk : Keep [.rdi, .rsi, .r11] u v := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₁.gpr (by simp [hr.2.2]), hk₀.gpr (by simp [hr.1, hr.2.1])], k₁.2.1.trans hk₀.2.1, k₁.2.2.trans hk₀.2.2⟩
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have hsrc : src + H.P.N ≤ oRsa := by unfold oDig oRsa at *; omega_using [ho]
  have hdg : oDig + H.P.N ≤ oRsa := by unfold oDig oRsa; omega_using [hN]
  refine WP.call (k := Proof.MdHashTable.X86_64.digestK hH.md)
    (Proof.MdHashTable.X86_64.digest_verified hH.shape hdk.mx) hdk.sp (by simp [Impl.MdHashTable.X86_64.digest, Code.depth])
    (rd := [⟨off S src, H.P.N⟩]) (wr := [⟨off S oDig, H.P.N⟩]) ?_ ?_ (Lv.cov hdg) ?_
  · simp only [Proof.MdHashTable.X86_64.digestK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), hdi, hsi, Lv.rsp, true_and]
    have := Lv.Sw
    refine ⟨Offset.disjoint S (by unfold oDig at *; omega_using [ho]) (by unfold oDig oRsa at *; omega_using [ho, this])
      (by unfold oDig oRsa at *; omega_using [hN, this]),
      Region.Disjoint.sub_right L.dR8 (Offset.sub_base S hsrc), Region.Disjoint.sub_right L.dR8 (Offset.sub_base S hdg)⟩
  · exact Covers.append_left (Covers.right (Lv.cov hsrc)) (Covers.right (Lv.cov hdg))
  · intro u' hrd hwr hcs hF hnc ⟨s₂, hm₂, _, hpost⟩
    simp only [Proof.MdHashTable.X86_64.digestK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      hdi, hsi] at hpost
    simp only [Impl.MdHashTable.X86_64.digest, Code.depth] at hF
    rw [Lv.rsp] at hF
    obtain ⟨L', R'⟩ := Lv.after_call Rv (rgs := [(oDig, H.P.N)])
      (by simp only [List.mem_singleton]; rintro p rfl; exact hdg) (by simpa [regs] using frame_ret hF)
      (hcs .rsp (by decide)) hwr
    refine ⟨L', ⟨fun r hr => ?_, hrd.trans hk.2.1, hwr.trans hk.2.2⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases hb : r = .rbx ∨ r = .rbp
      · rcases hb with rfl | rfl
        all_goals rw [hcs _ (by decide), hk.gpr (by decide)]
      · simp only [not_or] at hb
        rw [hnc r (hdk.cl r (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2, hb.1, hb.2])), hk.gpr (by simp [hr.1, hr.2.1, hr.2.2.2.2.1])]
    · have RE := Rep.callEntry Lv Rv
      have hst : hH.md.stateAt v.callEntry.mem (off S src) = hH.md.stateAt u.mem (off S src) := by
        rw [stateAt_rep hH Rv RE (o := src) hsrc (fun _ _ => rfl), hm]
      rw [hst] at hpost
      refine (congrArg (fun V' => Rep u'.mem F S V' W) (funext fun o => ?_)).mp R'
      by_cases hin : oDig ≤ o ∧ o < oDig + H.P.N
      · have hl : (hH.md.digest (hH.md.stateAt u.mem (off S src))).length = H.P.N := hH.md.digest_length _
        have hsub : (off S o - off S oDig).toNat = o - oDig := by
          have e : off S o = off S oDig + BitVec.ofNat 64 (o - oDig) := by
            show off S o = off (off S oDig) (o - oDig)
            rw [off_off, Nat.add_sub_cancel' hin.1]
          have hlt : o - oDig < 2 ^ 64 := by unfold oDig at hin; omega_using [hin, hN]
          rw [e, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
        simp only [inR_cons, inR_nil, or_false, hin, and_self, ite_true, ← hm₂, hpost, WriteBytes.writeBytes, hsub, hl,
          show o - oDig < H.P.N by omega_using [hin], ite_true]
      · simp only [inR_cons, inR_nil, or_false, hin, ite_false]

theorem digestOut_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {dn : String} {f : MdFns} (hT : HT H dn f W u.syms) (hdk : DigOK H) :
    WP isa (digestOut f) u fun u' => Lay u' F S ∧ Keep [.rdi, .rsi, .r8, .r9, .r11, .rax] u u' ∧
      Rep u'.mem F S (fun o => if oDig ≤ o ∧ o < oDig + H.P.N then
        (hH.md.digest (hH.md.stateAt u.mem (off S oSel))).getD (o - oDig) 0 else V o) W :=
  digestAt_ok hH L R (by have := hH.N_le; unfold oSel oDig; omega_using [this]) hT hdk

end VG.Proof.RsaPss.X86_64
