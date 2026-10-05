import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Layout

/-!
# Deterministic ECDSA on x86 (32-bit): addresses and registers

Our arguments as the code loads them (`argM`), the code that sets one
register to an address in `scratch` or the frame or to a constant (`Upd`),
and the bytes of a region a frame of writes misses.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont.X86 (wp_movS)

/-- Argument `i` of the layout. -/
def Lay.a {dn : Nat} (L : Lay dn) : Nat → BitVec 32
  | 0 => L.a0
  | 1 => L.a1
  | 2 => L.a2
  | _ => L.a3

/-- The bytes of a region a frame of writes misses. -/
theorem bytesAt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- `p + d` does not wrap. -/
theorem toNat_add_of {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt h]

/-- The 76 bytes below the frame, which the calls use. -/
theorem Ctx.below_eq {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} {u : State} (hL : L.Ok)
    (hc : Ctx L g m₀ u) : below (u.gpr .esp) 76 = ⟨L.B, 76⟩ := by
  rw [hc.esp, hL.below_F]

theorem Lay.Ok.low_scr {dn : Nat} {L : Lay dn} (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 76⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h₂)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- Our arguments, in the frame's body. -/
theorem Ctx.argv {u : State} (hc : Ctx L g m₀ u) {i : Nat} (hi : i < 4) :
    u.mem.readW (L.B + BitVec.ofNat 64 (276 + 4 * i)) 32 = L.a i := by
  match i, hi with
  | 0, _ => exact hc.pOut
  | 1, _ => exact hc.pD
  | 2, _ => exact hc.pDg
  | 3, _ => exact hc.pScr

theorem argM_eq (i : Nat) : argM i = .mem ⟨.esp, 200 + 4 * i⟩ := rfl

/-- `argM i` reads our argument `i`. -/
theorem Ctx.readArg {u : State} (hL : L.Ok) (hc : Ctx L g m₀ u) {i : Nat} (hi : i < 4) :
    readSrc u (argM i) = some (L.a i) := by
  have e : addr L.F (200 + 4 * i) = L.B + BitVec.ofNat 64 (276 + 4 * i) := by
    rw [hL.addrF (by omega), show 76 + (200 + 4 * i) = 276 + 4 * i by omega]
  rw [argM_eq, readSrc_mem hc.esp (by rw [e]; exact hc.inArgs hi hL), e, hc.argv hi]

/-! ## Code that sets one register -/

/-- `u'` is `u` with only the register `d` (not `esp`, and the flags)
changed, to `v`. -/
structure Upd {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (u : State) (d : Reg) (v : BitVec 32)
    (u' : State) : Prop where
  ctx : Ctx L g m₀ u'
  mem : u'.mem = u.mem
  val : u'.gpr d = v
  keep : ∀ r, r ≠ d → u'.gpr r = u.gpr r

theorem Ctx.set (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp)
    (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr) (hm : u'.mem = u.mem) (hk : ∀ r, r ≠ d → u'.gpr r = u.gpr r) :
    Ctx L g m₀ u' :=
  hc.regs hL hrd hwr hm (hk .esp (Ne.symm hd))

theorem Upd.of_wp {u u' : State} {d : Reg} {v : BitVec 32} (hL : L.Ok) (hc : Ctx L g m₀ u) (hd : d ≠ .esp)
    (h : VG.X86.Wp.Upd u u' d v) : Upd L g m₀ u d v u' :=
  ⟨hc.set hL hd h.rd h.wr h.mem h.other, h.mem, h.gpr, h.other⟩

theorem Upd.trans {u u' u'' : State} {d : Reg} {v w : BitVec 32} (hL : L.Ok) (hd : d ≠ .esp)
    (h₁ : VG.X86.Wp.Upd u u' d v) (h₂ : VG.X86.Wp.Upd u' u'' d w) (hc : Ctx L g m₀ u) :
    Upd L g m₀ u d w u'' :=
  ⟨hc.set hL hd (h₂.rd.trans h₁.rd) (h₂.wr.trans h₁.wr) (h₂.mem.trans h₁.mem)
      fun r hr => (h₂.other r hr).trans (h₁.other r hr),
    h₂.mem.trans h₁.mem, h₂.gpr, fun r hr => (h₂.other r hr).trans (h₁.other r hr)⟩

/-- `d ← scratch + a`. -/
theorem scr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) (a : Nat) :
    WP isa (.block (Cfg.scr d a)) u (Upd L g m₀ u d (L.a3 + BitVec.ofNat 32 a)) := by
  refine wp_movS (hc.readArg hL (i := 3) (by omega)) fun _ v₁ _ => wp_addi fun u₂ v₂ => WP.block_nil ?_
  rw [v₁.gpr] at v₂
  exact Upd.trans hL hd v₁ v₂ hc

/-- `d ← esp + o`, an address in the frame. -/
theorem fr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) (o : Nat) :
    WP isa (.block (Cfg.fr d o)) u (Upd L g m₀ u d (L.F + BitVec.ofNat 32 o)) := by
  refine wp_mov fun _ v₁ => wp_addi fun u₂ v₂ => WP.block_nil ?_
  rw [v₁.gpr, hc.esp] at v₂
  exact Upd.trans hL hd v₁ v₂ hc

/-- `d ← v`. -/
theorem movi_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) (v : BitVec 32) :
    WP isa (.block [.mov d (.imm v)]) u (Upd L g m₀ u d v) :=
  wp_movi fun _ v₁ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- `d ← argument i`. -/
theorem arg_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) {i : Nat} (hi : i < 4) :
    WP isa (.block [.mov d (argM i)]) u (Upd L g m₀ u d (L.a i)) :=
  wp_movS (hc.readArg hL hi) fun _ v₁ _ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- Two pieces of code, each setting one register. -/
theorem upd_append {is js : List Instr} {u : State} {d e : Reg} {v w : BitVec 32}
    (h₁ : WP isa (.block is) u (Upd L g m₀ u d v))
    (h₂ : ∀ u', Ctx L g m₀ u' → WP isa (.block js) u' (Upd L g m₀ u' e w)) {Q : State → Prop}
    (hQ : ∀ u'', Ctx L g m₀ u'' → u''.mem = u.mem → u''.gpr e = w →
      (∀ r, r ≠ e → r ≠ d → u''.gpr r = u.gpr r) → (e ≠ d → u''.gpr d = v) → Q u'') :
    WP isa (.block (is ++ js)) u Q := by
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun u' h => WP.mono (h₂ u' h.ctx) fun u'' h' => hQ u'' h'.ctx (h'.mem.trans h.mem) h'.val
    (fun r hre hrd => (h'.keep r hre).trans (h.keep r hrd)) fun hne => (h'.keep d hne.symm).trans h.val

end VG.Proof.Ecdsa.Rfc6979.X86
