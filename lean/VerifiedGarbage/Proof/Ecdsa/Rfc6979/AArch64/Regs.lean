import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Layout
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on AArch64: addresses and registers

The code that sets one register to an address in `scratch` or the frame or
to a constant (`Upd`), the stack below `sp` the calls use, and the bytes of
a region a frame of writes misses.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-- The 16 bytes below the frame, which the calls use. -/
theorem below16 (B : Addr) : below (B + BitVec.ofNat 64 16) 16 = ⟨B, 16⟩ := by
  show (⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 16, 16⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

/-- A fact `simp` has reduced to `True`, or an equation of definitionally equal sides. -/
macro "atriv" : tactic => `(tactic| first | trivial | rfl)

theorem ne_cs {r d : Reg} (hr : r ∈ preserved) (hd : d ∉ preserved) : r ≠ d :=
  fun e => hd (e ▸ hr)

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

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The stack below `sp` a call with at most one frame uses: the 16 bytes below the frame. -/
theorem Ctx.below_eq {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} {u : State}
    (hc : Ctx L g m₀ u) : below u.sp 16 = ⟨L.B, 16⟩ := by
  rw [hc.sp, below16]

/-- Code that writes no callee-saved register and calls nothing keeps them. -/
theorem WP.keepCs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : (instrs c).all (fun i => preserved.all fun r => dstOf i != some r) = true)
    (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, Exec.sp he, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn)⟩
  have h₁ := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using h₁

/-- Code that keeps the permissions and the callee-saved registers, and
writes only safe regions, keeps `Ctx`. -/
theorem Ctx.of_keep {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem} (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {is : List Instr} {ws : List Region} {Q : State → Prop}
    (h : WP isa (.block is) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ Frame ws t.mem t'.mem ∧ Q t')
    (hk : (instrs (.block is : Prog isa)).all (fun i => preserved.all fun r => dstOf i != some r) = true)
    (hs : ∀ r ∈ ws, Safe L r) :
    WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Frame ws t.mem t'.mem ∧ Q t' :=
  WP.mono (WP.keepCs h hk rfl) fun _ ⟨⟨hrd, hwr, hf, hq⟩, hsp, hcs⟩ =>
    ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hcs r hr) hf hs, hf, hq⟩

/-! ## Code that sets one register -/

/-- `u'` is `u` with only the register `d`, not callee-saved, (and the
flags) changed, to `v`. -/
structure Upd {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (u : State) (d : Reg) (v : BitVec 64)
    (u' : State) : Prop where
  ctx : Ctx L g m₀ u'
  mem : u'.mem = u.mem
  val : u'.gpr d = v
  keep : ∀ r, r ≠ d → u'.gpr r = u.gpr r

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem Ctx.set (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved)
    (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr) (hm : u'.mem = u.mem) (hsp : u'.sp = u.sp)
    (hk : ∀ r, r ≠ d → u'.gpr r = u.gpr r) : Ctx L g m₀ u' :=
  hc.regs hL hrd hwr hm hsp fun r hr _ => hk r (ne_cs hr hd)

/-- `d ← scratch + a`. -/
theorem scr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {a : Nat}
    (ha : a < 4096) :
    WP isa (.block (Cfg.scr d a)) u (Upd L g m₀ u d (L.scr + BitVec.ofNat 64 a)) := by
  have h200 := hc.inFr (d := 200) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.scr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read,
    Size.bits, BitVec.setWidth_eq, hc.sp, Offset.add_add, Nat.reduceAdd, Nat.reduceMod, Nat.reduceLT, and_self,
    h200, ite_true, Option.map_some, read8, hc.pScr, RegUpd.gpr_write_self, ha, Option.some.injEq,
    exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
    fun r hr => ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ hr, RegUpd.gpr_write_of_ne _ _ _ hr]
  · rw [RegUpd.gpr_write_of_ne _ _ _ hr, RegUpd.gpr_write_of_ne _ _ _ hr]

/-- `d ← sp + o`, an address in the frame. -/
theorem fr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {o : Nat}
    (ho : o < 4096) :
    WP isa (.block (Cfg.fr d o)) u (Upd L g m₀ u d (L.B + BitVec.ofNat 64 (16 + o))) := by
  apply WP.of_runBlock
  simp only [Cfg.fr, runBlock_cons, runStep_some, runBlock_nil, exec, ho, ite_true, hc.sp, Offset.add_add,
    Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

theorem movz_val {n : Nat} (hn : n < 2 ^ 16) :
    (BitVec.ofNat 16 n).setWidth Size.x.bits <<< (16 * 0) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  show n % 2 ^ 16 % 2 ^ 64 = n % 2 ^ 64
  omega

/-- `d ← n`. -/
theorem movz_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ preserved) {n : Nat}
    (hn : n < 2 ^ 16) :
    WP isa (.block [.movz .x d (BitVec.ofNat 16 n) 0]) u (Upd L g m₀ u d (BitVec.ofNat 64 n)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide, ite_true,
    movz_val hn, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- Two pieces of code, each setting one register. -/
theorem upd_append {is js : List Instr} {u : State} {d e : Reg} {v w : BitVec 64}
    (h₁ : WP isa (.block is) u (Upd L g m₀ u d v))
    (h₂ : ∀ u', Ctx L g m₀ u' → WP isa (.block js) u' (Upd L g m₀ u' e w)) {Q : State → Prop}
    (hQ : ∀ u'', Ctx L g m₀ u'' → u''.mem = u.mem → u''.gpr e = w →
      (∀ r, r ≠ e → r ≠ d → u''.gpr r = u.gpr r) → (e ≠ d → u''.gpr d = v) → Q u'') :
    WP isa (.block (is ++ js)) u Q := by
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun u' h => WP.mono (h₂ u' h.ctx) fun u'' h' => hQ u'' h'.ctx (h'.mem.trans h.mem) h'.val
    (fun r hre hrd => (h'.keep r hre).trans (h.keep r hrd)) fun hne => (h'.keep d hne.symm).trans h.val

end VG.Proof.Ecdsa.Rfc6979.AArch64
