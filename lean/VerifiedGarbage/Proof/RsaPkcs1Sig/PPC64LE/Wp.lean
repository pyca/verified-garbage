module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# RSASSA-PKCS1-v1_5 on PPC64LE: one instruction at a time

Untrusted: everything here is checked by Lean. The rules of
`Proof/ChaCha20Poly1305/PPC64LE/Wp.lean`, stated as on AArch64
(`Proof/MlKem/AArch64/Wp.lean`): an instruction that writes a register `d`
leaves a state `Only [d]`-related to the one before (every other register,
memory, the permissions, the stack pointer and the link register as they
were) with the value it wrote, and a store leaves one `MemTo` its memory. A
run of them composes into `Only rs` or, with stores, `Keep rs` (memory
aside).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE

open VG VG.PPC64LE
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd)

/-- `s'` is `s` but for the registers `rs`. -/
structure Only (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

/-- `s'` is `s` but for the registers `rs` and memory. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

/-- `s'` is `s` with memory `m`. -/
structure MemTo (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

namespace Only

theorem refl (rs : List Reg) (s : State) : Only rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only rs s₁ s₂) (h₂ : Only rs' s₂ s₃) :
    Only (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1],
   h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, h₂.lr.trans h₁.lr⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Only rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp, h.lr⟩

/-- A register not in `rs` is kept. -/
theorem get {rs : List Reg} {s s' : State} (h : Only rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

theorem keep {rs : List Reg} {s s' : State} (h : Only rs s s') : Keep rs s s' := ⟨h.gpr, h.rd, h.wr, h.sp, h.lr⟩

end Only

namespace Keep

theorem refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs' s₂ s₃) :
    Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1],
   h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, h₂.lr.trans h₁.lr⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Keep rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp, h.lr⟩

theorem get {rs : List Reg} {s s' : State} (h : Keep rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

end Keep

theorem MemTo.keep {s s' : State} {m : Mem} (h : MemTo s s' m) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, h.lr⟩

theorem only_of_upd {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr, u.sp, u.lr⟩

theorem memTo_of_mupd {s s' : State} {m : Mem} (u : Mupd s s' m) : MemTo s s' m :=
  ⟨u.gpr, u.mem, u.rd, u.wr, u.sp, u.lr⟩

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Only [d] s s' → s'.gpr d = BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_li h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_addi {d n : Reg} {imm : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n + BitVec.ofNat 64 imm → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) (h : imm < 2 ^ 15 := by decide) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_addi hn h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_subi {d n : Reg} {imm : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n - BitVec.ofNat 64 imm → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) (h : imm ≤ 2 ^ 15 := by decide) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_subi hn h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_add {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n + s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_add fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n - s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_sub fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_and {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_and fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_or {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_or fun s' u => k s' (only_of_upd u) u.gpr

/-- `mov d n`, an `or` of `n` with itself. -/
theorem wp_mov {d n : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.AesGcm.PPC64LE.mov d n :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_or fun s' u => k s' (only_of_upd u) (by rw [u.gpr, BitVec.or_self])

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_xor fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_lsr {d n : Reg} {sh : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n >>> sh → WP isa (.block is) s' Q) (h : sh < 64 := by decide) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_lsr h fun s' u => k s' (only_of_upd u) u.gpr

/-- `srwi d, n, sh`, a shift of the low word, zero-extended. -/
theorem wp_lsrw {d n : Reg} {sh : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = ((s.gpr n).setWidth 32 >>> sh).setWidth 64 → WP isa (.block is) s' Q)
    (h : sh < 32 := by decide) :
    WP isa (.block (.lsr .w d n sh :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.WP.cons (exec_lsr_w h)
    (k _ (only_of_upd (ChaCha20Poly1305.PPC64LE.Upd.write _ _ _)) (ChaCha20Poly1305.PPC64LE.Upd.write _ _ _).gpr)

theorem wp_lsl {d n : Reg} {sh : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n <<< sh → WP isa (.block is) s' Q) (h : sh < 64 := by decide) :
    WP isa (.block (.lsl d n sh :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_lsl h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_addSp {d : Reg} {imm : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.sp + BitVec.ofNat 64 imm → WP isa (.block is) s' Q)
    (h : imm < 2 ^ 15 := by decide) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.WP.cons (by simp [exec, show imm < 32768 from h])
    (k _ (only_of_upd (ChaCha20Poly1305.PPC64LE.Upd.write _ _ _)) (ChaCha20Poly1305.PPC64LE.Upd.write _ _ _).gpr)

theorem wp_mflr {d : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.mflr d :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_mflr fun s' u => k s' (only_of_upd u) u.gpr

/-- `mtlr r`: only the link register changes. -/
theorem wp_mtlr {r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.lr = s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.mtlr r :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_mtlr fun s' u => k s' u.gpr u.mem u.rd u.wr u.sp u.lr

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr}
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Only [t] s s' → s'.gpr t = (s.mem a).setWidth 64 → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) (ho : off < 2 ^ 15 := by decide) :
    WP isa (.block (.lbz t n off :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_lbz hn ho ha hin fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr}
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Only [t] s s' → s'.gpr t = s.mem.readW a 64 → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) (ho : off < 2 ^ 15 ∧ off % 4 = 0 := by decide) :
    WP isa (.block (.load .d t n off :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_ld hn ho ha hin fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_stb {t n : Reg} {off : Nat} {a : Addr}
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', MemTo s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) (ho : off < 2 ^ 15 := by decide) :
    WP isa (.block (.stb t n off :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_stb hn ho ha hout fun s' u => k s' (memTo_of_mupd u)

theorem wp_std {t n : Reg} {off : Nat} {a : Addr}
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', MemTo s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) (ho : off < 2 ^ 15 ∧ off % 4 = 0 := by decide) :
    WP isa (.block (.store .d t n off :: is)) s Q :=
  ChaCha20Poly1305.PPC64LE.wp_std hn ho ha hout fun s' u => k s' (memTo_of_mupd u)

end

/-- `cmpldi r, 0` then `bne`. -/
theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0) := by
  show some _ = _
  simp only [State.read, Size.bits, BitVec.setWidth_eq]

/-- `cmpldi r, 0` then `beq`. -/
theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0) := by
  show some _ = _
  simp only [State.read, Size.bits, BitVec.setWidth_eq]

/-- `cmplwi r, 0` then `beq`. -/
theorem eval_zero_w (s : State) (r : Reg) :
    isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  show some _ = _
  simp only [State.read, Size.bits]

theorem ne_zero_iff {x : BitVec 64} : (x != 0) = decide (x.toNat ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h h0; exact h (BitVec.eq_of_toNat_eq (by simpa using h0))
  · intro h h0; exact h (by rw [h0]; rfl)

theorem ite_both {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (h₁ : WP isa th s Q) (h₂ : WP isa el s Q) : WP isa (.ite c th el) s Q := by
  cases b
  · exact WP.ite false hc (by simp) (fun _ => h₂)
  · exact WP.ite true hc (fun _ => h₁) (by simp)

/-- A do-while loop on `cmpldi cnt, 0; bne` whose body decrements `cnt`,
from `N > 0`: it runs `N` times. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 64) (hN0 : 0 < N)
    (Inv : Nat → State → Prop)
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 64 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1)
    {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 64 N) :
    WP isa (.loop body (.nonzero .d cnt)) s (Inv N) := by
  refine WP.loop (M := isa) (fun (k : Nat) (u : State) => ∃ i, k = N - i ∧ i < N ∧ Inv i u ∧
    u.gpr cnt = BitVec.ofNat 64 (N - i)) ?_ (N - 0) _ ⟨0, rfl, hN0, h0, by rw [hc, Nat.sub_zero]⟩
  rintro k u ⟨i, rfl, hi, hI, hcu⟩
  refine WP.mono (hbody i hi u hI hcu) fun u' ⟨hI', hc'⟩ => ?_
  have e : u'.gpr cnt = BitVec.ofNat 64 (N - (i + 1)) := by
    rw [hc', hcu]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have ev : isa.eval (.nonzero .d cnt) u' = some (decide (N - (i + 1) ≠ 0)) := by
    rw [eval_nonzero, e, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hd : i + 1 = N
  · left; exact ⟨ev.trans (by simp; omega), hd ▸ hI'⟩
  · right; exact ⟨ev.trans (by simp; omega), N - (i + 1), by omega, i + 1, rfl, by omega, hI', e⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE
