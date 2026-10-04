import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash

/-!
# Deterministic ECDSA on 32-bit ARM: addresses and registers

The code that sets one register to an address in `scratch` or the frame
(`scrAt_ok`, `addSp_ok`), and the addresses those registers hold.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.X25519.Arm (Upd Mupd wp_movw wp_mov wp_dp op2_reg op2_imm dpVal)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `add d, sp, #imm`. -/
theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 256)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 32 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.sp + BitVec.ofNat 32 imm))
    (by simp only [exec, h, ↓reduceIte]) (k _ (Upd.setReg _ _ _))

end

theorem bytesAt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `scratch + o` as an address. -/
theorem scrA (hL : L.Ok) {o : Nat} (ho : o < 8192) :
    State.addr (L.scr + BitVec.ofNat 32 o) = State.addr L.scr + BitVec.ofNat 64 o :=
  addr_add (by have := hL.nc; omega)

theorem movw_val {o : Nat} (ho : o < 2 ^ 16) : (BitVec.ofNat 16 o).setWidth 32 = BitVec.ofNat 32 o := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `d ← scratch + o`, through `r12`. -/
theorem scrAt_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {o : Nat} (ho : o < 2 ^ 16)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = L.scr + BitVec.ofNat 32 o →
      (∀ r, r ≠ d → r ≠ .r12 → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (scrAt d o ++ is)) t Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine wp_movw fun t₁ u₁ => ?_
  refine wp_dp (op2_reg _ _) fun t₂ u₂ => ?_
  have c₁ := hc.upd u₁ (by decide)
  refine k t₂ (c₁.upd u₂ hd) (by rw [u₂.mem, u₁.mem]) ?_ fun r h1 h2 => by rw [u₂.other _ h1, u₁.other _ h2]
  rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hc.r11, movw_val ho]
  rfl

/-- `d ← sp + o`, an address in the frame. -/
theorem addSp_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {o : Nat} (ho : o < 256)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = L.fp + BitVec.ofNat 32 o →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.addSp d o :: is)) t Q :=
  wp_addSp ho fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem (by rw [u₁.gpr, hc.sp]) u₁.other

/-- `d ← v`, a register set to a 16-bit constant. -/
theorem movw_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {v : Nat} (hv : v < 2 ^ 16)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = BitVec.ofNat 32 v →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.movw d (BitVec.ofNat 16 v) :: is)) t Q :=
  wp_movw fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem (by rw [u₁.gpr, movw_val hv]) u₁.other

/-- `d ← 0`. -/
theorem mov0_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = 0 →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.mov d (.imm 0) :: is)) t Q :=
  wp_mov (op2_imm (by decide)) fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem u₁.gpr u₁.other

/-- `d ← s`, a copy of a register. -/
theorem movr_ok {t : State} (hc : Ctx L g m₀ t) {d r : Reg} (hd : d ∉ ptrRegs) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = t.gpr r →
      (∀ q, q ≠ d → t'.gpr q = t.gpr q) → WP isa (.block is) t' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) t Q :=
  wp_mov (op2_reg _ _) fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem u₁.gpr u₁.other

end VG.Proof.Ecdsa.Rfc6979.Arm
