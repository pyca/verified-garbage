module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash
public import VerifiedGarbage.Proof.Framework.Arm.Dispatch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Deterministic ECDSA on 32-bit ARM: addresses and registers

The code that sets one register to an address in `scratch` or the frame
(`scrAt_ok`, `fpAdd_ok`), and the addresses those registers hold.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.X25519.Arm (Upd Mupd wp_movw wp_mov wp_dp op2_reg op2_imm op2_lsl dpVal)

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

/-- `d ← r8 + o`, an address in the frame. -/
theorem fpAdd_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {o : Nat}
    (ho : encodable (BitVec.ofNat 32 o) = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = L.fp + BitVec.ofNat 32 o →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.dp .add d .r8 (.imm (BitVec.ofNat 32 o)) :: is)) t Q :=
  wp_dp (op2_imm ho) fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem (by rw [u₁.gpr, dpVal, hc.r8]) u₁.other

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

/-! ## Flags -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `subs`, with its carry: set iff no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y))
    (by simp only [exec, ho, Option.map_some]) (k _ (Upd.subs _ _ _ _ _) rfl)

/-- `mov`, keeping the carry. -/
theorem wp_movC {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → s'.c = s.c → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some])
    (k _ (Upd.setReg _ _ _) rfl)

/-- `adc`. -/
theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0)))
    (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

end

/-! ## The hash function's sizes, from its code -/

/-- What the code's values need of the layout: the scalars' length, and the
hash function's code in `r6`. -/
def HOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.q = P.Q ∧ L.code = BitVec.ofNat 32 P.c

/-- `D`, from the code. -/
theorem code_D (P : RfcHash) : BitVec.ofNat 32 P.c &&& 0xfe = BitVec.ofNat 32 P.F.H.D := by
  simp only [RfcHash.c, code]
  rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    rw [h, h'] <;> decide

/-- `B`, from the code. -/
theorem code_B (P : RfcHash) : ((BitVec.ofNat 32 P.c &&& 1) <<< 6) + 64 = BitVec.ofNat 32 P.F.H.B := by
  simp only [RfcHash.c, code]
  rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    rw [h, h'] <;> decide

variable {P : RfcHash}

/-- `d ← D`, the hash function's output length. -/
theorem dOut_ok (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = BitVec.ofNat 32 P.F.H.D →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (Cfg.dOut d ++ is)) t Q :=
  wp_dp (op2_imm (by decide)) fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem
    (by rw [u₁.gpr, dpVal, hc.r6, hq.2]; exact code_D P) u₁.other

/-- `d ← B`, the hash function's block length. -/
theorem dBlk_ok (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = BitVec.ofNat 32 P.F.H.B →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (Cfg.dBlk d ++ is)) t Q := by
  simp only [Cfg.dBlk, List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun t₁ u₁ => wp_mov (op2_lsl (by decide)) fun t₂ u₂ =>
    wp_dp (op2_imm (by decide)) fun t₃ u₃ => ?_
  refine k t₃ (((hc.upd u₁ hd).upd u₂ hd).upd u₃ hd) (by rw [u₃.mem, u₂.mem, u₁.mem]) ?_
    fun r hr => by rw [u₃.other _ hr, u₂.other _ hr, u₁.other _ hr]
  rw [u₃.gpr, dpVal, u₂.gpr, u₁.gpr, dpVal, hc.r6, hq.2]
  exact code_B P

/-! ## The dispatch on the hash function -/

theorem Ctx.flags {t : State} (hc : Ctx L g m₀ t) {t' : State} (h : Proof.Dispatch.Arm.FlagsOnly t t') : Ctx L g m₀ t' := by
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact ⟨hc.rd, hc.wr, hc.sp, hc.r4, hc.r5, hc.r6, hc.r8, hc.r11, hc.saved, hc.frame⟩

/-- Distinct images, of distinct elements. -/
theorem nodup_map_inj {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => absurd hx (List.not_mem_nil)
  | a :: l, hn, x, y, hx, hy, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp hx with h₁ | hx <;> rcases List.mem_cons.mp hy with h₂ | hy
    · rw [h₁, h₂]
    · rw [h₁] at he; exact absurd he.symm (hn.1 y hy)
    · rw [h₂] at he; exact absurd he (hn.1 x hx)
    · exact nodup_map_inj hn.2 hx hy he

/-- The keys of a dispatch on the hash functions `hs`. -/
theorem disp_keys (hs : List Impl.Pbkdf2.Whole.Arm.Fns) (f : Impl.Pbkdf2.Whole.Arm.Fns → Prog isa) :
    Proof.Dispatch.keys (hs.map fun F => (code F, f F)) = hs.map code := by
  simp only [Proof.Dispatch.keys, List.map_map]; rfl

/-- The code's dispatch runs the case of the run's hash function, from a
state with other flags. -/
theorem disp_wp (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {f : Impl.Pbkdf2.Whole.Arm.Fns → Prog isa}
    {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Proof.Dispatch.Arm.FlagsOnly t t' → WP isa (f P.F) t' Q) :
    WP isa ((cfgOf P).disp f) t Q := by
  have hsel : Proof.Dispatch.Arm.sel .r6 t = P.c := by
    simp only [Proof.Dispatch.Arm.sel, hc.r6, hq.2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := P.codes _ P.mem; show code P.F < 2 ^ 32; omega)
  refine Proof.Dispatch.chain_wp (Proof.Dispatch.Arm.tests .r6) _
    (by rw [disp_keys]; intro k hk; obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hk; exact P.codes F hF)
    (by rw [disp_keys, hsel]; exact List.mem_map_of_mem P.mem) (by rw [disp_keys]; exact P.nodup)
    fun c hm t' hr _ => ?_
  rw [hsel] at hm
  obtain ⟨F, hF, he⟩ := List.mem_map.mp hm
  obtain ⟨e₁, rfl⟩ := Prod.mk.inj he
  have : F = P.F := nodup_map_inj P.nodup hF P.mem e₁
  subst this
  exact h t' (hc.flags hr) hr

end VG.Proof.Ecdsa.Rfc6979.Arm
