import VerifiedGarbage.Proof.X25519.X86.Ops
import VerifiedGarbage.Impl.X25519.X86.Field32

/-!
# `vg_gf25519_r32_mul` on x86 (32-bit): copies through pointers

`xfer rs rd fs fd n` moves `n` words from `[rs + fs k]` to `[rd + fd k]`
through `eax`. With `rs` and `rd` pointing into the working space at `x`
(`x + ps`, `x + pd`), it copies the words at `a + 4 k` to `o + 4 k` of the
working space (`xfer_ok`): `copyIn` (`[a]` through a pointer, to a fixed
offset through `edi`) and `copyOut` (the result, from a fixed offset through
`edx = ws`, to `[o]` through a pointer) are transfers.
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86

variable {W : Nat}

theorem addr_add (x : BitVec 32) (p d : Nat) : addr (x + BitVec.ofNat 32 p) d = addr x (p + d) := by
  simp only [addr, BitVec.ofNat_add, BitVec.add_assoc]

/-- `n` words from `[rs + fs k]` to `[rd + fd k]`, through `eax`. -/
def xfer (rs rd : Reg) (fs fd : Nat → Nat) (n : Nat) : List Instr :=
  (List.range n).flatMap fun k => [.mov .eax (.mem (at_ rs (fs k))), .store (at_ rd (fd k)) .eax]

theorem copyIn_eq (r : Reg) (d : Nat) : copyIn r d = xfer r .edi (fun k => 4 * k) (fun k => d + 4 * k) 8 := rfl

theorem copyOut_eq : copyOut = xfer .edx .ecx (fun k => opA + 4 * k) (fun k => 4 * k) 8 := rfl

/-- What a transfer keeps: the registers but `eax`, and the regions. -/
structure XKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem XKeep.refl (s : State) : XKeep s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem XKeep.trans {s t u : State} (h₁ : XKeep s t) (h₂ : XKeep t u) : XKeep s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

/-- The pointers and offsets of a transfer: word `k` of `[x + a]` to word
`k` of `[x + o]`, two elements of the working space that do not overlap. -/
structure XArgs (W : Nat) (x : BitVec 32) (rs rd : Reg) (fs fd : Nat → Nat) (ps pd a o : Nat)
    (s : State) : Prop where
  fit : x.toNat + W ≤ 2 ^ 32
  wr : scR W x ∈ s.wr
  src : s.gpr rs = x + BitVec.ofNat 32 ps
  dst : s.gpr rd = x + BitVec.ofNat 32 pd
  srcA : rs ≠ .eax
  dstA : rd ≠ .eax
  fs : ∀ k < 8, ps + fs k = a + 4 * k
  fd : ∀ k < 8, pd + fd k = o + 4 * k
  ha : a + 32 ≤ W
  ho : o + 32 ≤ W
  apart : a + 32 ≤ o ∨ o + 32 ≤ a

theorem XArgs.keep {x : BitVec 32} {rs rd : Reg} {fs fd : Nat → Nat} {ps pd a o : Nat} {s t : State}
    (h : XArgs W x rs rd fs fd ps pd a o s) (k : XKeep s t) : XArgs W x rs rd fs fd ps pd a o t :=
  ⟨h.fit, k.wr ▸ h.wr, (k.gpr _ h.srcA).trans h.src, (k.gpr _ h.dstA).trans h.dst, h.srcA, h.dstA, h.fs, h.fd,
    h.ha, h.ho, h.apart⟩

theorem xfer_step {x : BitVec 32} {rs rd : Reg} {fs fd : Nat → Nat} {ps pd a o : Nat} {s₀ s : State}
    (h : XArgs W x rs rd fs fd ps pd a o s) {n : Nat} (hn : n < 8) (hk : XKeep s₀ s)
    (hf : Frame [sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, wd s.mem x (o + 4 * j) = wd s₀.mem x (a + 4 * j)) :
    WP isa (.block [.mov .eax (.mem (at_ rs (fs n))), .store (at_ rd (fd n)) .eax]) s fun s' =>
      XKeep s₀ s' ∧ Frame [sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, wd s'.mem x (o + 4 * j) = wd s₀.mem x (a + 4 * j) := by
  have hfit := h.fit
  have ha := h.ha; have ho := h.ho
  have es : addr (x + BitVec.ofNat 32 ps) (fs n) = addr x (a + 4 * n) := by
    rw [addr_add, h.fs n hn]
  have ed : addr (x + BitVec.ofNat 32 pd) (fd n) = addr x (o + 4 * n) := by
    rw [addr_add, h.fd n hn]
  refine Wp.wp_ldm h.src (by
    rw [es]; exact ⟨_, List.mem_append_right _ h.wr, scR_contains hfit (by omega_using [ha, hn]) (by decide)⟩)
    fun s₁ u₁ => ?_
  have hd₁ : s₁.gpr rd = x + BitVec.ofNat 32 pd := by rw [u₁.other _ h.dstA]; exact h.dst
  refine Wp.wp_stm hd₁ (by
    rw [ed, u₁.wr]; exact ⟨_, h.wr, scR_contains hfit (by omega_using [ho, hn]) (by decide)⟩)
    fun s₂ u₂ => WP.block_nil ?_
  rw [es] at u₁; rw [ed] at u₂
  have hr : wd s.mem x (a + 4 * n) = wd s₀.mem x (a + 4 * n) :=
    wd_frame1 hf hfit (by omega_using [ho, hn]) (by omega_using [ha, hn])
      (by rcases h.apart with e | e <;> omega_using [e, hn])
  refine ⟨hk.trans ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩,
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact frame_write1 (frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.gpr, u₁.mem]
    by_cases e : j = n
    · subst e; rw [wd_write_self]; exact hr
    · rw [wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem xfer_ok {x : BitVec 32} {rs rd : Reg} {fs fd : Nat → Nat} {ps pd a o : Nat} {s : State}
    (h : XArgs W x rs rd fs fd ps pd a o s) : ∀ n ≤ 8,
    WP isa (.block (xfer rs rd fs fd n)) s fun s' =>
      XKeep s s' ∧ Frame [sub x o (4 * n)] s.mem s'.mem ∧
        ∀ j < n, wd s'.mem x (o + 4 * j) = wd s.mem x (a + 4 * j)
  | 0, _ => WP.block_nil ⟨XKeep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [xfer, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (xfer_ok h n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      xfer_step (h.keep k₁) (by omega_using [hn]) k₁ f₁ w₁)

/-- A transfer of an element: its value, and what changes. -/
theorem xfer8_ok {x : BitVec 32} {rs rd : Reg} {fs fd : Nat → Nat} {ps pd a o : Nat} {s : State}
    (h : XArgs W x rs rd fs fd ps pd a o s) :
    WP isa (.block (xfer rs rd fs fd 8)) s fun s' =>
      XKeep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧ fe s'.mem x o = fe s.mem x a :=
  WP.mono (xfer_ok h 8 (Nat.le_refl _)) fun _ ⟨k, f, w⟩ =>
    ⟨k, f, num_congr fun j hj => by
      show (wd _ x (o + 4 * j)).toNat = (wd _ x (a + 4 * j)).toNat; rw [w j hj]⟩

end VG.Proof.X25519.X86.Field32
