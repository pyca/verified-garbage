module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Recombine
public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Weave
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Formula
import VerifiedGarbage.Proof.X25519.AArch64.Word.Small
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on AArch64: an iteration's field operations, with `DA` and `CB` in AdvSIMD

Untrusted: everything here is checked by Lean. `Hybrid.stepFields` leaves in
slots 1–4 what the four-word step's operations do (`Word.core`), writing only the
slots and the vector buffers (`FKeep`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 (Slot offset FieldOp fieldCode)
open VG.Proof.Ed25519.AArch64 (Keep env evalOps evalOp F fieldCode_ok Outside ofs clob)
open VG.Proof.X25519.AArch64.Word (core mulA24_ok)
open VG.Proof.Ed25519.AArch64 (word)
open VG.Impl.X25519.AArch64.Hybrid (LBUF vectorA scalarA stepFields recombine tail)
open VG.Impl.X25519.AArch64.Neon (FBUF)

/-- Memory changed at most in the slots and the vector buffers. -/
def HMem (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < 64 ∨ (768 ≤ ofs base x ∧ ofs base x < 784) ∨ 1104 ≤ ofs base x) → m' x = m x

theorem HMem.refl (base : Addr) (m : Mem) : HMem base m m := fun _ _ => rfl

theorem HMem.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : HMem base m₁ m₂) (h₂ : HMem base m₂ m₃) :
    HMem base m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem HMem.of_slots {base : Addr} {m m' : Mem} (h : Outside base 64 704 m m') : HMem base m m' :=
  fun x hx => h x (by omega)

theorem HMem.of_bufs {base : Addr} {m m' : Mem} (h : Outside base 784 320 m m') : HMem base m m' :=
  fun x hx => h x (by omega)

/-- What an iteration's field operations keep. -/
structure FKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : HMem base s.mem t.mem

theorem FKeep.trans {base : Addr} {s t u : State} (h : FKeep base s t) (k : FKeep base t u) : FKeep base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem FKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : FKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, HMem.of_slots h.mem⟩

theorem FKeep.scratch {base : Addr} {s t : State} (h : FKeep base s t) (hs : Scratch s base) : Scratch t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem HMem.outside {base : Addr} {m m' : Mem} (h : HMem base m m') : Outside base 64 1040 m m' :=
  fun x hx => h x (by omega)

theorem consts_of_outside {base : Addr} {m m' : Mem} (h : Outside base 64 1040 m m') (hc : Consts m base) :
    Consts m' base := by
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨fun e he => ?_, fun e he => ?_, fun c hc' => ?_⟩
  · rw [Outside.word' h (by simp only [VG.Impl.X25519.AArch64.Neon.M26, VG.Impl.X25519.AArch64.Neon.CONST]; omega)
      (by simp only [VG.Impl.X25519.AArch64.Neon.M26, VG.Impl.X25519.AArch64.Neon.CONST]; omega)]
    exact c1 e he
  · rw [Outside.word' h (by simp only [VG.Impl.X25519.AArch64.Neon.M25, VG.Impl.X25519.AArch64.Neon.CONST]; omega)
      (by simp only [VG.Impl.X25519.AArch64.Neon.M25, VG.Impl.X25519.AArch64.Neon.CONST]; omega)]
    exact c2 e he
  · rw [Outside.nw h (by simp only [VG.Impl.X25519.AArch64.Neon.C19, VG.Impl.X25519.AArch64.Neon.CONST]; omega)
      (by simp only [VG.Impl.X25519.AArch64.Neon.C19, VG.Impl.X25519.AArch64.Neon.CONST]; omega)]
    exact c3 c hc'

theorem HMem.consts {base : Addr} {m m' : Mem} (h : HMem base m m') (hc : Consts m base) : Consts m' base :=
  consts_of_outside h.outside hc



/-- The limbs at `LBUF`: bounded, with values `X` (lane 0) and `Y` (lane 1). -/
def LimbsIn (m : Mem) (base : Addr) (X Y : Fe) : Prop :=
  (∀ k < 10, (word m base (LBUF + 16 * k)).toNat < 2 ^ 27 ∧ (word m base (LBUF + 16 * k + 8)).toNat ≤ limbB k) ∧
  toFe (val fun k => (word m base (LBUF + 16 * k)).toNat) = X ∧
  toFe (val fun k => (word m base (LBUF + 16 * k + 8)).toNat) = Y

theorem env_of_bufs {base : Addr} {m m' : Mem} (h : Outside base 784 320 m m') : env m' base = env m base := by
  funext i
  simp only [env, F]
  rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem below_offset (i : Slot) : Below (offset i) := by
  simp only [Below, offset, FBUF]; omega

theorem toFe_fe (m : Mem) (base : Addr) (i : Slot) : toFe (feAt m base (offset i)) = env m base i := rfl

/-- `DA` and `CB` in AdvSIMD: their limbs at `LBUF`. -/
theorem vectorA_ok {s : State} {base : Addr} (hs : Scratch s base) (hc : Consts s.mem base) :
    WP isa (.block vectorA) s fun t =>
      FKeep base s t ∧ env t.mem base = env s.mem base ∧
      LimbsIn t.mem base (env s.mem base 8 * env s.mem base 5) (env s.mem base 7 * env s.mem base 6) := by
  refine WP.mono (prod2_ok hs hc (o := LBUF) ⟨by decide, by decide, by decide⟩ (below_offset 8) (below_offset 5)
    (below_offset 7) (below_offset 6)) fun t ⟨tw, to, tg, tr, tww, tsp, _⟩ => ?_
  have to' : Outside base 784 320 s.mem t.mem := by simpa only [LBUF, FBUF] using to
  have w0 : ∀ k < 10, (word t.mem base (LBUF + 16 * k)).toNat =
      prodLimbs s.mem base (fun e => if e = 0 then offset 8 else offset 7) (fun e => if e = 0 then offset 5 else offset 6) 0 k :=
    fun k hk => by have := tw k hk 0 (by decide); simpa only [Nat.mul_zero, Nat.add_zero] using this
  have w1 : ∀ k < 10, (word t.mem base (LBUF + 16 * k + 8)).toNat =
      prodLimbs s.mem base (fun e => if e = 0 then offset 8 else offset 7) (fun e => if e = 0 then offset 5 else offset 6) 1 k :=
    fun k hk => by have := tw k hk 1 (by decide); simpa only [Nat.mul_one] using this
  refine ⟨⟨fun r _ => by rw [tg], tr, tww, tsp, HMem.of_bufs to'⟩, env_of_bufs to', ⟨fun k hk => ⟨?_, ?_⟩, ?_, ?_⟩⟩
  · rw [w0 k hk]; exact prodLimbs_lt _ _ _ _ _ k hk
  · rw [w1 k hk]; exact prodLimbs_le _ _ _ _ _ k hk
  · rw [← toFe_fe, ← toFe_fe]
    apply toFe_mul
    have e : (val fun k => (word t.mem base (LBUF + 16 * k)).toNat) =
        val (prodLimbs s.mem base (fun e => if e = 0 then offset 8 else offset 7)
          (fun e => if e = 0 then offset 5 else offset 6) 0) := by
      simp only [val, S10]; rw [w0 0 (by decide), w0 1 (by decide), w0 2 (by decide), w0 3 (by decide),
        w0 4 (by decide), w0 5 (by decide), w0 6 (by decide), w0 7 (by decide), w0 8 (by decide), w0 9 (by decide)]
    rw [e, prodLimbs_val]; rfl
  · rw [← toFe_fe, ← toFe_fe]
    apply toFe_mul
    have e : (val fun k => (word t.mem base (LBUF + 16 * k + 8)).toNat) =
        val (prodLimbs s.mem base (fun e => if e = 0 then offset 8 else offset 7)
          (fun e => if e = 0 then offset 5 else offset 6) 1) := by
      simp only [val, S10]; rw [w1 0 (by decide), w1 1 (by decide), w1 2 (by decide), w1 3 (by decide),
        w1 4 (by decide), w1 5 (by decide), w1 6 (by decide), w1 7 (by decide), w1 8 (by decide), w1 9 (by decide)]
    rw [e, prodLimbs_val]; rfl


theorem LimbsIn.of_keep {base : Addr} {m m' : Mem} {X Y : Fe} (h : Outside base 64 704 m m') (hL : LimbsIn m base X Y) :
    LimbsIn m' base X Y := by
  have hw : ∀ k < 10, ∀ e < 2, word m' base (LBUF + 16 * k + 8 * e) = word m base (LBUF + 16 * k + 8 * e) :=
    fun k hk e he => Outside.word' h (by simp only [LBUF]; omega) (by simp only [LBUF]; omega)
  have h0 : ∀ k < 10, word m' base (LBUF + 16 * k) = word m base (LBUF + 16 * k) := fun k hk => by
    simpa only [Nat.mul_zero, Nat.add_zero] using hw k hk 0 (by decide)
  have h1 : ∀ k < 10, word m' base (LBUF + 16 * k + 8) = word m base (LBUF + 16 * k + 8) := fun k hk => by
    simpa only [Nat.mul_one] using hw k hk 1 (by decide)
  obtain ⟨hb, hx, hy⟩ := hL
  refine ⟨fun k hk => by rw [h0 k hk, h1 k hk]; exact hb k hk, ?_, ?_⟩
  · rw [← hx, val, val]; exact congrArg toFe (S10_congr fun k hk => by rw [h0 k hk])
  · rw [← hy, val, val]; exact congrArg toFe (S10_congr fun k hk => by rw [h1 k hk])

/-- `X₃ := DA + CB`, `Z₃ := DA - CB` from the limbs. -/
theorem recombs_ok {s : State} {base : Addr} (hs : Scratch s base) {X Y : Fe} (hL : LimbsIn s.mem base X Y) :
    WP isa (.block (recombine false (offset 3) ++ recombine true (offset 4))) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (Function.update (env s.mem base) 3 (X + Y)) 4 (X - Y) := by
  obtain ⟨hb, hx, hy⟩ := hL
  rw [WP.block_append_iff]
  refine WP.mono (recombine_ok hs false (by decide) (by decide) (by decide) hb) fun t ⟨kt, ot, et⟩ => ?_
  have ht : Scratch t base := kt.scr hs
  have hL' := LimbsIn.of_keep kt.mem ⟨hb, hx, hy⟩
  obtain ⟨hb', hx', hy'⟩ := hL'
  refine WP.mono (recombine_ok ht true (by decide) (by decide) (by decide) hb') fun u ⟨ku, ou, eu⟩ => ?_
  refine ⟨kt.trans ku, ?_⟩
  rw [VG.Proof.Ed25519.AArch64.env_update 4 ou, VG.Proof.Ed25519.AArch64.env_update 3 ot, eu, et]
  congr 1
  · congr 1
    rw [← hx, ← hy, val_limbSum_add]
    exact toFe_add rfl
  · have hsub := val_limbSum_sub t.mem base (fun k hk => Nat.le_of_lt (Nat.lt_of_le_of_lt (hb' k hk).2 (bias_lt k hk).1))
    rw [← hx', ← hy']
    apply toFe_sub
    rw [hsub, Nat.mul_comm 4 P, Nat.add_mul_mod_self_left]


theorem scalarA_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block scalarA) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps [.add 2 9 2, .mul 2 11 2]
        (Function.update (evalOps [.sqr 9 5, .sqr 10 6, .sub 11 9 10, .mul 1 9 10] (env s.mem base)) 2
          (evalOps [.sqr 9 5, .sqr 10 6, .sub 11 9 10, .mul 1 9 10] (env s.mem base) 11 * 121665)) := by
  rw [scalarA, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (mulA24_ok (ka.scr hs) 2 11) fun b ⟨kb, eb⟩ => ?_
  refine WP.mono (fieldCode_ok _ (kb.scr (ka.scr hs))) fun t ⟨kt, et⟩ => ?_
  refine ⟨ka.trans (kb.trans kt), ?_⟩
  rw [et, eb, ea]

/-- `tail`: the last three field operations of the four-word step. -/
theorem tail_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block tail) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps [.sqr 3 3, .sqr 4 4, .mul 4 0 4] (env s.mem base) := by
  rw [tail, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.sqrMulField_ok (ka.scr hs) 4 0 4) fun t ⟨kt, et⟩ => ?_
  refine ⟨ka.trans kt, ?_⟩
  rw [et, ea]
  simp only [evalOps, List.foldl, evalOp, Function.update_idem, Function.update_self,
    Function.update_of_ne (show (0 : Slot) ≠ 4 by decide)]

/-- An iteration's field operations: the four-word step's results in slots 1–4. -/
theorem stepFields_ok {s : State} {base : Addr} (hs : Scratch s base) (hc : Consts s.mem base)
    (h18 : env s.mem base 18 = 121665) :
    WP isa (.block stepFields) s fun t =>
      FKeep base s t ∧ Consts t.mem base ∧
      env t.mem base 1 = (core (env s.mem base)).x2 ∧ env t.mem base 2 = (core (env s.mem base)).z2 ∧
      env t.mem base 3 = (core (env s.mem base)).x3 ∧ env t.mem base 4 = (core (env s.mem base)).z3 ∧
      env t.mem base 0 = env s.mem base 0 ∧ env t.mem base 18 = env s.mem base 18 := by
  rw [stepFields, List.append_assoc (_ ++ _) (recombine false _) (recombine true _), WP.block_append_iff,
    WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka, ea⟩ => ?_
  have ha : Scratch a base := ka.scr hs
  have hw : WP isa (.block (VG.Impl.AArch64Weave.weave scalarA vectorA)) a fun c => ∃ b : State,
      Keep base a b ∧ env b.mem base = evalOps [.add 2 9 2, .mul 2 11 2]
        (Function.update (evalOps [.sqr 9 5, .sqr 10 6, .sub 11 9 10, .mul 1 9 10] (env a.mem base)) 2
          (evalOps [.sqr 9 5, .sqr 10 6, .sub 11 9 10, .mul 1 9 10] (env a.mem base) 11 * 121665)) ∧
      FKeep base b c ∧ env c.mem base = env b.mem base ∧
      LimbsIn c.mem base (env b.mem base 8 * env b.mem base 5) (env b.mem base 7 * env b.mem base 6) :=
    Interleave.WP.weave indeps_A (WP.mono (scalarA_ok ha) fun b ⟨kb, eb⟩ =>
      WP.mono (vectorA_ok (kb.scr ha) ((HMem.of_slots (ka.trans kb).mem).consts hc)) fun c ⟨kc, ec, lc⟩ =>
        ⟨b, kb, eb, kc, ec, lc⟩)
  refine WP.mono hw fun c ⟨b, kb, eb, kc, ec, lc⟩ => ?_
  have hc3 : Scratch c base := kc.scratch (kb.scr ha)
  refine WP.mono (recombs_ok hc3 lc) fun d ⟨kd, ed⟩ => ?_
  refine WP.mono (tail_ok (kd.scr hc3)) fun t ⟨kt, et⟩ => ?_
  have kall : FKeep base s t :=
    ((((FKeep.of_keep ka).trans (FKeep.of_keep kb)).trans kc).trans (FKeep.of_keep kd)).trans (FKeep.of_keep kt)
  refine ⟨kall, kall.mem.consts hc, ?_⟩
  rw [et, ed, ec, eb, ea]
  simp only [core]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  rw [h18]
  rfl

end VG.Proof.X25519.AArch64.Hybrid
