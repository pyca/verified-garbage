module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontTail
public import VerifiedGarbage.Proof.Weierstrass.X86.MontBody
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Montgomery arithmetic as functions on x86 (32-bit): the functions

`mulFn`, `addFn` and `subFn` (`Impl/Weierstrass/X86/Mont.lean`), from a state
that has their arguments on the stack (`Pre`): the working space `ws`
(`arg 0`, 8192 writable bytes), the offsets `o`, `a` and `b` (`arg 1` to
`arg 3`) below the own working space, the arguments readable and apart from
`ws`, and the return address apart from it. Each restores `ebx`, `esi`, `edi`
and `ebp`, writes only `[o]` and its own working space (`Outs`), and leaves
the number the contract says at `[o]`: `mulFn_ok`, `addFn_ok`, `subFn_ok`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

/-- The working space, `arg 0`. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

/-- What the functions' contracts give them, by argument. -/
structure Pre (k : Nat) (s : State) : Prop where
  rd : s.rd = [⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨wsOf s, 8192⟩]
  ws_fit : (arg s 0).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  args_ws : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨wsOf s, 8192⟩
  ret_ws : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 8192⟩
  k0 : 0 < k
  k9 : k ≤ 9
  fo : (arg s 1).toNat + 8 * k ≤ own k
  fa : (arg s 2).toNat + 8 * k ≤ own k
  fb : (arg s 3).toNat + 8 * k ≤ own k

/-- Memory outside ranges within the first `size` bytes of `base` is
unchanged outside those bytes. -/
theorem Outs.frame {base : Addr} {size : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ size) : Frame [⟨base, size⟩] m m' := by
  intro x hx
  refine h x fun r hr => .inr ?_
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains, ofs] at this ⊢
  have := hrs r hr
  omega_arith

variable {k : Nat} {s : State}

theorem Pre.argAddr_eq (hp : Pre k s) {i : Nat} (hi : i < 4) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.sp_fit
  change addr (s.gpr .esp) (4 + 4 * i) = addr (s.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega_using [hi, this]), addr_eq (by omega_using [this]), BitVec.add_assoc, ← BitVec.ofNat_add]

theorem Pre.arg_contains (hp : Pre k s) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  rw [hp.argAddr_eq hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

/-- An argument, in a state with the stack pointer and the readable regions
of `s`, whose memory differs from `s`'s only within the working space. -/
theorem Pre.readArg (hp : Pre k s) {t : State} (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd)
    (hf : Frame [⟨wsOf s, 8192⟩] s.mem t.mem) {i : Nat} (hi : i < 4) :
    readSrc t (.mem (at_ .esp (4 + 4 * i))) = some (arg s i) := by
  show t.load32 (t.ea (at_ .esp (4 + 4 * i))) = _
  obtain hea : t.ea (at_ .esp (4 + 4 * i)) = argAddr s i := by
    change addr (t.gpr .esp) (4 + 4 * i) = addr (s.gpr .esp) (4 + 4 * i); rw [hsp]
  rw [hea, State.load32, ite_eq_left_iff.mpr fun h => absurd ⟨_, by rw [hrd, hp.rd]; simp, hp.arg_contains hi⟩ h]
  refine congrArg some ?_
  exact hf.readW (hp.arg_contains hi) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.args_ws)
    (by decide)

theorem Outside.frame {base : Addr} {size o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (hon : o + n ≤ size) : Frame [⟨base, size⟩] m m' :=
  Outs.frame (Outs.of_outside h (List.mem_singleton_self _)) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hon

theorem saveAt_le {k : Nat} (h0 : 0 < k) (h9 : k ≤ 9) : saveAt k + 16 ≤ 4096 ∧ own k + 64 * k = 4096 := by
  simp only [saveAt, tmpAt, own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega_arith

/-- A store through `r` holding the working space's base. -/
theorem ea_base {t : State} {r : Reg} {W : BitVec 32} (hr : t.gpr r = W) (hW : W.toNat + 8192 ≤ 2 ^ 32)
    {d : Nat} (hd : d < 8192) : t.ea (at_ r d) = off (W.setWidth 64) d := by
  change addr (t.gpr r) d = _
  rw [hr, addr_eq (by omega_using [hW, hd])]

/-- After `mulEntry`: `ebp` the working space, `esi` and `edi` pointing to
`[b]` and `[a]`, the caller's registers saved. -/
theorem mulEntry_ok (hp : Pre k s) :
    WP isa (.block (mulEntry k)) s fun u =>
      Bx u (wsOf s) 8192 ∧ Ptr u .esi (arg s 3).toNat ∧ Ptr u .edi (arg s 2).toNat ∧
      Keeps [.eax, .esi, .edi, .ebp] s u ∧ u.gpr .esp = s.gpr .esp ∧
      Outside (wsOf s) (saveAt k) 16 s.mem u.mem ∧
      w32 u.mem (wsOf s) (saveAt k) = (s.gpr .ebx).toNat ∧
      w32 u.mem (wsOf s) (saveAt k + 4) = (s.gpr .esi).toNat ∧
      w32 u.mem (wsOf s) (saveAt k + 8) = (s.gpr .edi).toNat ∧
      w32 u.mem (wsOf s) (saveAt k + 12) = (s.gpr .ebp).toNat := by
  have hn := hp.ws_fit
  obtain hws : (wsOf s).toNat = (arg s 0).toNat := by simp only [wsOf, BitVec.toNat_setWidth]; omega_arith
  obtain hn' : (wsOf s).toNat + 8192 ≤ 2 ^ 32 := by rw [hws]; exact hn
  obtain ⟨hsv, -⟩ := saveAt_le hp.k0 hp.k9
  obtain hwr : ∀ {t : State}, t.wr = s.wr → ∀ {d}, d + 4 ≤ 8192 → InRegions t.wr (off (wsOf s) d) 4 :=
    fun {t} ht {d} hd => ⟨_, by rw [ht, hp.wr]; exact List.mem_singleton_self _,
      Offset.contains_base _ hd (by omega_using [hd])⟩
  simp only [mulEntry]
  refine wp_movS (hp.readArg rfl rfl (Frame.refl _ _) (i := 0) (by decide)) fun s₁ u₁ _ => ?_
  refine wp_storeS (ea_base u₁.gpr hn (d := saveAt k) (by omega_using [hsv])) (hwr u₁.wr (by omega_using [hsv])) fun s₂ m₂ => ?_
  refine wp_storeS (ea_base (by rw [m₂.gpr]; exact u₁.gpr) hn (d := saveAt k + 4) (by omega_using [hsv]))
    (hwr (by rw [m₂.wr, u₁.wr]) (by omega_using [hsv])) fun s₃ m₃ => ?_
  refine wp_storeS (ea_base (by rw [m₃.gpr, m₂.gpr]; exact u₁.gpr) hn (d := saveAt k + 8) (by omega_using [hsv]))
    (hwr (by rw [m₃.wr, m₂.wr, u₁.wr]) (by omega_using [hsv])) fun s₄ m₄ => ?_
  refine wp_storeS (ea_base (by rw [m₄.gpr, m₃.gpr, m₂.gpr]; exact u₁.gpr) hn (d := saveAt k + 12) (by omega_using [hsv]))
    (hwr (by rw [m₄.wr, m₃.wr, m₂.wr, u₁.wr]) (by omega_using [hsv])) fun s₅ m₅ => ?_
  obtain g₅ : s₅.gpr = s₁.gpr := by rw [m₅.gpr, m₄.gpr, m₃.gpr, m₂.gpr]
  obtain hm₅ : s₅.mem = ((((s.mem.writeW (off (wsOf s) (saveAt k)) (s.gpr .ebx)).writeW
      (off (wsOf s) (saveAt k + 4)) (s.gpr .esi)).writeW (off (wsOf s) (saveAt k + 8)) (s.gpr .edi)).writeW
      (off (wsOf s) (saveAt k + 12)) (s.gpr .ebp)) := by
    rw [m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₄.gpr, m₃.gpr, m₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
  obtain O₅ : Outside (wsOf s) (saveAt k) 16 s.mem s₅.mem := by
    rw [hm₅]
    exact (((writeW32_outside _ _ _ (by omega_using [hsv])).mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hsv])).mono (by omega_using []) (by omega_using []))).trans
      (((writeW32_outside _ _ _ (by omega_using [hsv])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hsv])).mono (by omega_using []) (by omega_using [])))
  obtain F₅ := Outside.frame O₅ (size := 8192) (by omega_using [hsv])
  obtain esp₅ : s₅.gpr .esp = s.gpr .esp := by rw [g₅, u₁.other _ (by decide)]
  obtain rd₅ : s₅.rd = s.rd := by rw [m₅.rd, m₄.rd, m₃.rd, m₂.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [m₅.wr, m₄.wr, m₃.wr, m₂.wr, u₁.wr]
  refine wp_movS rfl fun s₆ u₆ _ => ?_
  refine wp_movS (hp.readArg (by rw [u₆.other _ (by decide), esp₅]) (by rw [u₆.rd, rd₅])
    (by rw [u₆.mem]; exact F₅) (i := 3) (by decide)) fun s₇ u₇ _ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_movS (hp.readArg (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), esp₅])
    (by rw [u₈.rd, u₇.rd, u₆.rd, rd₅]) (by rw [u₈.mem, u₇.mem, u₆.mem]; exact F₅) (i := 2) (by decide))
    fun s₉ u₉ _ => ?_
  refine wp_addS rfl fun s₁₀ u₁₀ _ => WP.block_nil ?_
  obtain mem₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  obtain ebp₁₀ : s₁₀.gpr .ebp = arg s 0 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      g₅, u₁.gpr]
  obtain hof : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by simp
  obtain bx : Bx s₁₀ (wsOf s) 8192 := by
    refine ⟨by rw [ebp₁₀], by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅, hp.wr]; exact List.mem_singleton_self _, ?_⟩
    exact hn'
  refine ⟨bx, ?_, ?_, ?_, ?_, by rw [mem₁₀]; exact O₅, ?_, ?_, ?_, ?_⟩
  · change s₁₀.gpr .esi = s₁₀.gpr .ebp + _
    rw [ebp₁₀, hof, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₇.other _ (by decide),
      u₆.gpr, g₅, u₁.gpr, BitVec.add_comm]
  · change s₁₀.gpr .edi = s₁₀.gpr .ebp + _
    rw [ebp₁₀, hof, u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.gpr, g₅, u₁.gpr, BitVec.add_comm]
  · refine ⟨fun r hr => ?_, by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅], by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [u₁₀.other _ h3, u₉.other _ h3, u₈.other _ h2, u₇.other _ h2, u₆.other _ h4, g₅, u₁.other _ h1]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), esp₅]
  all_goals rw [mem₁₀, hm₅]
  · rw [w32_write_ne hn' (by omega_using [hsv]) (by omega_using [hsv]) (by omega_using []), w32_write_ne hn' (by omega_using [hsv]) (by omega_using [hsv]) (by omega_using []),
      w32_write_ne hn' (by omega_using [hsv]) (by omega_using [hsv]) (by omega_using []), w32_write_self]
  · rw [w32_write_ne hn' (by omega_using [hsv]) (by omega_using [hsv]) (by omega_using []), w32_write_ne hn' (by omega_using [hsv]) (by omega_using [hsv]) (by omega_using []),
      w32_write_self]
  · rw [w32_write_ne hn' (by omega_using [hsv]) (by omega_using [hsv]) (by omega_using []), w32_write_self]
  · rw [w32_write_self]

/-! ## The conditional subtraction -/

theorem Bx.of_other {base : Addr} {size : Nat} {t : State} {r : Reg} (hb : Bx s base size) (h : ∀ q, q ≠ r → t.gpr q = s.gpr q)
    (hr : r ≠ .ebp) (hw : t.wr = s.wr) : Bx t base size :=
  ⟨by rw [h _ hr.symm]; exact hb.ebp, hw ▸ hb.wr, hb.nowrap⟩

theorem Outside.readW32 {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  BitVec.eq_of_toNat_eq (h.w32 hd hd')

theorem diffsI_eq (m src tmp N : Nat) : diffsI m src tmp N =
    chainK .eax (fun j => .mem (bp (src + 4 * j))) .sub .sbb (fun j => .imm (mw m j))
      (fun j => bp (tmp + 4 * j)) N := rfl

/-- `diffsI`, `maskTop` and `outPtr`: the number `T` below `2m` at `src`
(`N` words and a top word), its difference with `m` at `tmp`, the mask in
`eax` selecting the one that is `T mod m`, and `ecx = ws + O` for the
offset `O` at `[esp + 8]`. -/
theorem csubPre_ok {base : Addr} {size : Nat} (hb : Bx s base size) {m src tmp N : Nat} {O : BitVec 32}
    {L : List Instr} {Q : State → Prop} (hN : 0 < N) (hm : m < 2 ^ (32 * N)) (hst : src + 4 * N + 4 ≤ tmp)
    (htmp : tmp + 4 * N ≤ size) (hT : val32 s.mem base src (N + 1) < 2 * m)
    (hO : ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd = s.rd → Outside base tmp (4 * N) s.mem t.mem →
      readSrc t (.mem (at_ .esp 8)) = some O)
    (hk : ∀ u, Keeps [.eax, .ecx] s u → Outside base tmp (4 * N) s.mem u.mem → Ptr u .ecx O.toNat →
      ∀ b : Bool, u.gpr .eax = (if b then BitVec.allOnes 32 else 0) →
      val32 u.mem base (if b then tmp else src) N = val32 s.mem base src (N + 1) % m → WP isa (.block L) u Q) :
    WP isa (.block (diffsI m src tmp N ++ (maskTop src N ++ (outPtr ++ L)))) s Q := by
  have hn := hb.nowrap
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega_arith⟩
  have hX : SrcOk (fun j => .mem (bp (src + 4 * j))) (fun j => s.mem.readW (off base (src + 4 * j)) 32) .eax
      base tmp (N' + 1) s := fun j hj t ht hrd hwr O' => by
    dsimp only
    rw [readSrc_bp (hb.of_other ht (by decide) hwr) (d := src + 4 * j) (by omega_using [hst, htmp, hj]), Outside.readW32 O' (by omega_using [hst, hj]) (by omega_using [hn, hst, htmp, hj])]
  have hY : SrcOk (fun j => .imm (mw m j)) (fun j => mw m j) .eax base tmp (N' + 1) s :=
    fun _ _ _ _ _ _ _ => rfl
  have hD : DstOk (fun j => bp (tmp + 4 * j)) .eax base tmp (N' + 1) s := fun j hj t ht hwr =>
    have hbt := hb.of_other ht (by decide) hwr
    ⟨hbt.ea (by omega_using [htmp, hj]), hbt.write (by omega_using [htmp, hj])⟩
  rw [diffsI_eq]
  refine WP.block_append (WP.mono (chainKSub_ok hX hY hD (by omega_using [hn, htmp]) N' (Nat.le_refl _))
    fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  refine WP.block_append (WP.mono (maskTop_ok hb₁ hc (src := src) (N := N' + 1) (by omega_using [hst, htmp]))
    fun s₂ ⟨M₂, mem₂, K₂⟩ => ?_)
  have hb₂ := hb₁.of_keeps K₂ (by decide)
  simp only [outPtr, List.cons_append, List.nil_append]
  have K₂' : Keeps [.eax] s s₂ := K₁.trans K₂
  refine wp_movS (hO s₂ (K₂'.1 _ (by decide)) K₂'.2.1 (by rw [mem₂]; exact O₁)) fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  have K₄ : Keeps [.eax, .ecx] s s₄ := ((K₂'.mono (rs' := [.eax, .ecx]) (by decide)).widen u₃.keeps).widen u₄.keeps
  have mem₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, mem₂]
  refine hk s₄ K₄ (by rw [mem₄]; exact O₁) ?_ (!decide (w32 s₁.mem base (src + 4 * (N' + 1)) < c.toNat)) ?_ ?_
  · change s₄.gpr .ecx = s₄.gpr .ebp + _
    rw [u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), M₂]
  · rw [mem₄]
    have top : w32 s₁.mem base (src + 4 * (N' + 1)) = w32 s.mem base (src + 4 * (N' + 1)) :=
      O₁.w32 (by omega_using [hst]) (by omega_using [hn, hst, htmp])
    have ev : val32 s.mem base src (N' + 1 + 1) =
        val32 s.mem base src (N' + 1) + 2 ^ (32 * (N' + 1)) * w32 s.mem base (src + 4 * (N' + 1)) :=
      val32_succ _ _ _ _
    have hsrc₁ : val32 s₁.mem base src (N' + 1) = val32 s.mem base src (N' + 1) := O₁.val32 (by omega_using [hst]) (by omega_using [hn, hst, htmp])
    rw [yVal_val32, yVal_mw, Nat.mod_eq_of_lt hm] at V₁
    rw [top, ev, ← csub_arith (X := 2 ^ (32 * (N' + 1))) hm (val32_lt _ _ _ _) (by rw [← ev]; exact hT)
      (b := c) (by rw [V₁])]
    cases hd : decide (w32 s.mem base (src + 4 * (N' + 1)) < c.toNat)
    · have : ¬ w32 s.mem base (src + 4 * (N' + 1)) < c.toNat := of_decide_eq_false hd
      simp only [Bool.not_false, ite_true, this, ite_false]
    · have : w32 s.mem base (src + 4 * (N' + 1)) < c.toNat := of_decide_eq_true hd
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, this, ite_true]
      exact hsrc₁

/-- Loads through `ebp` of words apart from `D`. -/
theorem bp_src {base : Addr} {size : Nat} (hb : Bx s base size) {r : Reg} {p D N : Nat} (hr : r ≠ .ebp)
    (hd : p + 4 * N ≤ D ∨ D + 4 * N ≤ p) (hps : p + 4 * N ≤ size) :
    SrcOk (fun j => .mem (bp (p + 4 * j))) (fun j => s.mem.readW (off base (p + 4 * j)) 32) r base D N s :=
  fun j hj t ht hrd hwr O' => by
    obtain hbt := hb.of_other ht hr hwr
    dsimp only
    rw [readSrc_bp hbt (d := p + 4 * j) (by omega_using [hps, hj]), Outside.readW32 O' (by omega_using [hd, hj]) (by have := hb.nowrap; omega_using [hps, hj, this])]

/-! ### The modulus masked in registers -/

theorem p256Field_eq {k m : Nat} (h : p256Field k m = true) : k = 4 ∧ m = p256Prime := by
  simpa only [p256Field, Bool.and_eq_true, beq_iff_eq] using h

theorem p256_maskWords {k m : Nat} (h : p256Field k m = true) : MaskWords m (2 * k) := by
  obtain ⟨rfl, rfl⟩ := p256Field_eq h
  unfold MaskWords
  decide

/-- `maskBit` and `maskedOut`: `[ecx] = [src] - m` or `[src] + m` under the
mask, `N` words, with the carry or borrow. -/
theorem maskedSub_ok {base : Addr} {size : Nat} (hb : Bx s base size) {m src po N : Nat} (hw : MaskWords m N)
    (hN : 0 < N) (hm : m < 2 ^ (32 * N)) (hpo : Ptr s .ecx po) {b : Bool}
    (hmk : s.gpr .eax = if b then BitVec.allOnes 32 else 0)
    (hsrc : src + 4 * N ≤ size) (ho : po + 4 * N ≤ size) (hso : po + 4 * N ≤ src ∨ src + 4 * N ≤ po) :
    WP isa (.block (maskBit ++ maskedOut .sub .sbb m src N)) s fun u =>
      Outside base po (4 * N) s.mem u.mem ∧ Keeps [.edx, .ebx] s u ∧
      ∃ c : Bool, val32 u.mem base po N + (if b then m else 0) = val32 s.mem base src N + 2 ^ (32 * N) * c.toNat := by
  have hn := hb.nowrap
  refine maskBit_ok hmk fun s₁ K₁ M₁ B₁ => ?_
  have hb₁ := hb.of_keeps K₁ (by decide)
  have hp₁ : Ptr s₁ .ecx po := hpo.of_keeps K₁ (by decide) (by decide)
  have C := chainKSub_ok (s := s₁) (r := .edx) (bp_src hb₁ (p := src) (D := po) (N := N) (by decide)
    (by omega_using [hso]) hsrc) (maskSrc_ok hw (by rw [K₁.1 _ (by decide)]; exact hmk) B₁)
    (fun j hj t ht hwr => by
      have hbt := hb₁.of_other ht (by decide) hwr
      have hpt : Ptr t .ecx po := by
        change t.gpr .ecx = t.gpr .ebp + _; rw [ht _ (by decide), ht _ (by decide)]; exact hp₁
      exact ⟨hbt.ea_ptr hpt (by omega_using [ho, hj]), hbt.write (by omega_using [ho, hj])⟩)
    (by omega_using [hn, ho]) (N - 1) (by omega_using [hN])
  rw [show N - 1 + 1 = N by omega_using [hN]] at C
  refine WP.mono C fun u ⟨O, ⟨c, _, V⟩, K⟩ => ⟨by rw [← M₁]; exact O,
    (K₁.mono (by decide)).trans (K.mono (by decide)), c, ?_⟩
  rw [maskSrc_yVal, yVal_mw, Nat.mod_eq_of_lt hm, yVal_val32, M₁] at V
  exact V

theorem maskedAdd_ok {base : Addr} {size : Nat} (hb : Bx s base size) {m src po N : Nat} (hw : MaskWords m N)
    (hN : 0 < N) (hm : m < 2 ^ (32 * N)) (hpo : Ptr s .ecx po) {b : Bool}
    (hmk : s.gpr .eax = if b then BitVec.allOnes 32 else 0)
    (hsrc : src + 4 * N ≤ size) (ho : po + 4 * N ≤ size) (hso : po + 4 * N ≤ src ∨ src + 4 * N ≤ po) :
    WP isa (.block (maskBit ++ maskedOut .add .adc m src N)) s fun u =>
      Outside base po (4 * N) s.mem u.mem ∧ Keeps [.edx, .ebx] s u ∧
      ∃ c : Bool, val32 u.mem base po N + 2 ^ (32 * N) * c.toNat = val32 s.mem base src N + (if b then m else 0) := by
  have hn := hb.nowrap
  refine maskBit_ok hmk fun s₁ K₁ M₁ B₁ => ?_
  have hb₁ := hb.of_keeps K₁ (by decide)
  have hp₁ : Ptr s₁ .ecx po := hpo.of_keeps K₁ (by decide) (by decide)
  have C := chainKAdd_ok (s := s₁) (r := .edx) (bp_src hb₁ (p := src) (D := po) (N := N) (by decide)
    (by omega_using [hso]) hsrc) (maskSrc_ok hw (by rw [K₁.1 _ (by decide)]; exact hmk) B₁)
    (fun j hj t ht hwr => by
      have hbt := hb₁.of_other ht (by decide) hwr
      have hpt : Ptr t .ecx po := by
        change t.gpr .ecx = t.gpr .ebp + _; rw [ht _ (by decide), ht _ (by decide)]; exact hp₁
      exact ⟨hbt.ea_ptr hpt (by omega_using [ho, hj]), hbt.write (by omega_using [ho, hj])⟩)
    (by omega_using [hn, ho]) (N - 1) (by omega_using [hN])
  rw [show N - 1 + 1 = N by omega_using [hN]] at C
  refine WP.mono C fun u ⟨O, ⟨c, _, V⟩, K⟩ => ⟨by rw [← M₁]; exact O,
    (K₁.mono (by decide)).trans (K.mono (by decide)), c, ?_⟩
  rw [maskSrc_yVal, yVal_mw, Nat.mod_eq_of_lt hm, yVal_val32, M₁] at V
  exact V

/-- What the mask `b` of the conditional subtraction of `m` from the number
at `src` says: which of the number and the difference is reduced, or, if the
difference is not kept, whether the number is at least `m`. -/
def Sel (k m src : Nat) (base : Addr) (mem : Mem) (b : Bool) : Prop :=
  if p256Field k m then
    (b = true ∧ m ≤ val32 mem base src (2 * k + 1)) ∨ (b = false ∧ val32 mem base src (2 * k + 1) < m)
  else val32 mem base (if b then tmpAt k else src) (2 * k) = val32 mem base src (2 * k + 1) % m

theorem cmp_arith {t top m P D c : Nat} {T : Nat} (hT : t + P * top = T) (hTm : T < 2 * m) (hm : m < P)
    (hD : D < P) (ht : t < P) (hc : c ≤ 1) (hV : D + m = t + P * c) : (top < c → T < m) ∧ (¬ top < c → m ≤ T) := by
  have h1 : top ≤ 1 := by
    rcases Nat.lt_or_ge top 2 with h | h
    · omega_using [h]
    · have := Nat.mul_le_mul_left P h
      omega_using [this, hT, hTm, hm]
  have e1 : top = 0 ∨ top = 1 := by omega_using [h1]
  have e2 : c = 0 ∨ c = 1 := by omega_using [hc]
  rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;>
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hT hV <;>
    constructor <;> intro h <;> omega_using [hT, hV, hTm, hm, hD, ht, h]

theorem csel_arith {t top m P R T : Nat} {b c : Bool} (hT : t + P * top = T) (hTm : T < 2 * m) (hm : m < P)
    (hR : R < P) (ht : t < P) (hb : (b = true ∧ m ≤ T) ∨ (b = false ∧ T < m))
    (hV : R + (if b then m else 0) = t + P * c.toNat) : R = T % m := by
  have h1 : top ≤ 1 := by
    rcases Nat.lt_or_ge top 2 with h | h
    · omega_using [h]
    · have := Nat.mul_le_mul_left P h
      omega_using [this, hT, hTm, hm]
  have e1 : top = 0 ∨ top = 1 := by omega_using [h1]
  rcases hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  · rw [Nat.mod_eq_sub_mod hb, Nat.mod_eq_of_lt (by omega_using [hTm, hb])]
    rcases e1 with rfl | rfl <;> cases c <;>
      simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Bool.toNat_true, Bool.toNat_false, ite_true] at hT hV <;>
      omega_using [hT, hV, hTm, hm, hR, ht, hb]
  · rw [Nat.mod_eq_of_lt hb]
    rcases e1 with rfl | rfl <;> cases c <;>
      simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true,
        ite_false] at hT hV <;>
      omega_using [hT, hV, hTm, hm, hR, ht, hb]

/-- `csubHead`: the mask in `eax` of the conditional subtraction, and
`ecx = ws + O` for the offset `O` at `[esp + 8]`. -/
theorem csubHead_ok {base : Addr} {size : Nat} (hb : Bx s base size) {k m src : Nat} {O : BitVec 32}
    {L : List Instr} {Q : State → Prop} (hN : 0 < 2 * k) (hm : m < 2 ^ (32 * (2 * k)))
    (hst : src + 4 * (2 * k) + 4 ≤ tmpAt k) (htmp : tmpAt k + 4 * (2 * k) ≤ size)
    (hT : val32 s.mem base src (2 * k + 1) < 2 * m)
    (hO : ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd = s.rd → Outside base (tmpAt k) (4 * (2 * k)) s.mem t.mem →
      readSrc t (.mem (at_ .esp 8)) = some O)
    (hk : ∀ u, Keeps [.eax, .ecx] s u → Outside base (tmpAt k) (4 * (2 * k)) s.mem u.mem → Ptr u .ecx O.toNat →
      ∀ b : Bool, u.gpr .eax = (if b then BitVec.allOnes 32 else 0) → Sel k m src base u.mem b →
      val32 u.mem base src (2 * k + 1) = val32 s.mem base src (2 * k + 1) → WP isa (.block L) u Q) :
    WP isa (.block (csubHead k m src ++ L)) s Q := by
  have hn := hb.nowrap
  unfold csubHead
  by_cases hp : p256Field k m = true
  · rw [ite_eq_left hp, List.append_assoc, List.append_assoc]
    have C := cmpI_ok hb (m := m) (src := src) (2 * k - 1) (by omega_using [hst, htmp, hN])
    rw [show 2 * k - 1 + 1 = 2 * k by omega_using [hN]] at C
    refine WP.block_append (WP.mono C fun s₁ ⟨⟨c, D, hc, hD, V₁⟩, M₁, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    refine WP.block_append (WP.mono (maskTop_ok hb₁ hc (src := src) (N := 2 * k) (by omega_using [hst, htmp]))
      fun s₂ ⟨E₂, M₂, K₂⟩ => ?_)
    have K₂' : Keeps [.eax] s s₂ := K₁.trans K₂
    have mem₂ : s₂.mem = s.mem := M₂.trans M₁
    simp only [outPtr, List.cons_append, List.nil_append]
    refine wp_movS (hO s₂ (K₂'.1 _ (by decide)) K₂'.2.1 (by rw [mem₂]; exact Outside.refl _ _ _ _)) fun s₃ u₃ _ => ?_
    refine wp_addS rfl fun s₄ u₄ _ => ?_
    have K₄ : Keeps [.eax, .ecx] s s₄ := ((K₂'.mono (rs' := [.eax, .ecx]) (by decide)).widen u₃.keeps).widen u₄.keeps
    have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, mem₂]
    refine hk s₄ K₄ (by rw [mem₄]; exact Outside.refl _ _ _ _) ?_ (!decide (w32 s₁.mem base (src + 4 * (2 * k)) < c.toNat))
      ?_ ?_ (by rw [mem₄])
    · change s₄.gpr .ecx = s₄.gpr .ebp + _
      rw [u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.add_comm]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), E₂]
    · rw [Sel, ite_eq_left hp, mem₄]
      have ev := val32_succ s.mem base src (2 * k)
      rw [yVal_mw, Nat.mod_eq_of_lt hm] at V₁
      have A := cmp_arith ev.symm hT hm hD (val32_lt _ _ _ _) (Bool.toNat_le c) V₁
      rw [M₁]
      by_cases h : w32 s.mem base (src + 4 * (2 * k)) < c.toNat
      · exact .inr ⟨by simp only [h, decide_true, Bool.not_true], A.1 h⟩
      · exact .inl ⟨by simp only [h, decide_false, Bool.not_false], A.2 h⟩
  · rw [ite_eq_right hp, List.append_assoc, List.append_assoc]
    refine csubPre_ok hb hN hm hst htmp hT hO fun u K O' P b E V => hk u K O' P b E ?_
      (O'.val32 (by omega_using [hst]) (by omega_using [hn, hst, htmp]))
    rw [Sel, ite_eq_right hp, V, O'.val32 (by omega_using [hst]) (by omega_using [hn, hst, htmp])]

/-- `csubSel`: the number reduced, into `[ecx]`. -/
theorem csubSel_ok {base : Addr} {size : Nat} (hb : Bx s base size) {k m src po : Nat} (hN : 0 < 2 * k)
    (hm : m < 2 ^ (32 * (2 * k))) (hpo : Ptr s .ecx po) {b : Bool}
    (hmk : s.gpr .eax = if b then BitVec.allOnes 32 else 0) (hS : Sel k m src base s.mem b)
    (hT : val32 s.mem base src (2 * k + 1) < 2 * m) (hsrc : src + 4 * (2 * k) + 4 ≤ tmpAt k)
    (htmp : tmpAt k + 4 * (2 * k) ≤ size) (ho : po + 4 * (2 * k) ≤ src) :
    WP isa (.block (csubSel k m src)) s fun u =>
      Outside base po (4 * (2 * k)) s.mem u.mem ∧
      val32 u.mem base po (2 * k) = val32 s.mem base src (2 * k + 1) % m ∧
      Keeps [.edx, .ebx] s u ∧ (¬ p256Field k m = true → u.gpr .ebx = s.gpr .ebx) := by
  unfold csubSel
  by_cases hp : p256Field k m = true
  · rw [ite_eq_left hp]
    rw [Sel, ite_eq_left hp] at hS
    refine WP.mono (maskedSub_ok hb (p256_maskWords hp) hN hm hpo hmk (by omega_using [hsrc, htmp])
      (by omega_using [ho, hsrc, htmp]) (.inl ho)) fun u ⟨O, K, c, V⟩ => ⟨O, ?_, K, fun h => absurd hp h⟩
    exact csel_arith (val32_succ s.mem base src (2 * k)).symm hT hm (val32_lt _ _ _ _) (val32_lt _ _ _ _) hS V
  · rw [ite_eq_right hp]
    rw [Sel, ite_eq_right hp] at hS
    rw [show selectsP src (tmpAt k) (2 * k) = selP src (tmpAt k) (2 * k) from rfl]
    refine WP.mono (selP_ok hb hpo b hmk (2 * k) (by omega_using [hsrc, htmp]) htmp (by omega_using [ho, hsrc, htmp])
      (.inl ho) (by omega_using [ho, hsrc])) fun u ⟨O, V, K⟩ => ⟨O, V.trans hS, K.mono (by decide), fun _ => K.1 _ (by decide)⟩

/-- `restoreP`: the saved `ebp`, and `ebx` if it was saved. -/
theorem restoreP_ok {base : Addr} {size : Nat} (hb : Bx s base size) {k m : Nat} (hsv : saveAt k + 16 ≤ size) :
    WP isa (.block (restoreP k m)) s fun u => u.mem = s.mem ∧
      (∀ r, r ≠ .ebp → r ≠ .ebx → u.gpr r = s.gpr r) ∧
      u.gpr .ebp = s.mem.readW (off base (saveAt k + 12)) 32 ∧
      u.gpr .ebx = if p256Field k m then s.mem.readW (off base (saveAt k)) 32 else s.gpr .ebx := by
  unfold restoreP
  by_cases hp : p256Field k m = true
  · rw [ite_eq_left hp, ite_eq_left hp]
    simp only [restoreBP]
    refine wp_movS (readSrc_bp hb (d := saveAt k) (by omega_using [hsv])) fun s₁ u₁ _ => ?_
    have hb₁ := hb.of_keeps u₁.keeps (by decide)
    refine wp_movS (readSrc_bp hb₁ (d := saveAt k + 12) (by omega_using [hsv])) fun s₂ u₂ _ => WP.block_nil
      ⟨by rw [u₂.mem, u₁.mem], fun r h1 h2 => by rw [u₂.other _ h1, u₁.other _ h2], by rw [u₂.gpr, u₁.mem],
        by rw [u₂.other _ (by decide), u₁.gpr]⟩
  · rw [ite_eq_right hp, ite_eq_right hp]
    exact wp_movS (readSrc_bp hb (d := saveAt k + 12) (by omega_using [hsv])) fun s₁ u₁ _ => WP.block_nil
      ⟨u₁.mem, fun r h1 _ => u₁.other _ h1, u₁.gpr, u₁.other _ (by decide)⟩

/-! ## The product -/

theorem Outside.outs {base : Addr} {o n : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outside base o n m m')
    {r : Nat × Nat} (hr : r ∈ rs) (h1 : r.1 ≤ o) (h2 : o + n ≤ r.1 + r.2) : Outs base rs m m' :=
  fun x hx => h x (by have := hx r hr; omega_using [h1, h2, this])

/-- The ranges a function writes: `[o]` and its own working space. -/
abbrev outs (k : Nat) (s : State) : List (Nat × Nat) := [((arg s 1).toNat, 8 * k), (own k, 64 * k)]

theorem Pre.outs_le (hp : Pre k s) : ∀ r ∈ outs k s, r.1 + r.2 ≤ 8192 := by
  have := hp.fo; have := saveAt_le hp.k0 hp.k9
  intro r hr
  simp only [outs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only <;> omega_arith

/-- An argument, read from a state that wrote only `outs`. -/
theorem Pre.readArg' (hp : Pre k s) {t : State} (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd)
    (ho : Outs (wsOf s) (outs k s) s.mem t.mem) {i : Nat} (hi : i < 4) :
    readSrc t (.mem (at_ .esp (4 + 4 * i))) = some (arg s i) :=
  hp.readArg hsp hrd (Outs.frame ho hp.outs_le) hi

theorem own_mem (k : Nat) (s : State) : (own k, 64 * k) ∈ outs k s := by simp
theorem o_mem (k : Nat) (s : State) : ((arg s 1).toNat, 8 * k) ∈ outs k s := by simp

/-- `vg_<curve>_mul_mod_<p|n>`: `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulFn_ok {m : Nat} (hM : MulOk k m) (hp : Pre k s)
    (hB : val32 s.mem (wsOf s) (arg s 3).toNat (2 * k) < m) :
    WP isa (mulFn k m) s fun u => abiPreserved s u ∧ Outs (wsOf s) (outs k s) s.mem u.mem ∧
      val32 u.mem (wsOf s) (arg s 1).toNat (2 * k) < m ∧
      val32 u.mem (wsOf s) (arg s 1).toNat (2 * k) * 2 ^ (64 * k) % m =
        val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) * val32 s.mem (wsOf s) (arg s 3).toNat (2 * k) % m := by
  have hk0 := hp.k0
  have ⟨hsv, hown⟩ := saveAt_le hp.k0 hp.k9
  have := hp.fo; have := hp.fa; have := hp.fb
  obtain hsv' : saveAt k = own k + 24 * k + 4 := by simp only [saveAt, tmpAt]; omega_arith
  obtain htmp : tmpAt k = own k + 16 * k + 4 := by simp only [tmpAt]; omega_arith
  simp only [mulFn, csubOut, List.append_assoc]
  refine WP.seq (WP.mono (mulEntry_ok hp) fun s₁ ⟨bx₁, pb₁, pa₁, K₁, esp₁, O₁, v₁, v₂, v₃, v₄⟩ => ?_)
  have hn := bx₁.nowrap
  obtain hB₁ : val32 s₁.mem (wsOf s) (arg s 3).toNat (2 * k) < m := by
    rw [O₁.val32 (by omega_using [this, hsv']) (by omega_using [hown])]; exact hB
  obtain hL : MulLayB k 8192 (arg s 2).toNat (arg s 3).toNat (own k) := ⟨by omega_arith, by omega_arith, by omega_arith⟩
  refine WP.seq (WP.mono (mulBody_ok bx₁ hM pa₁ pb₁ hL hB₁)
    fun s₂ ⟨O₂, K₂, T₂, U, hU⟩ => ?_)
  obtain bx₂ := bx₁.of_keeps K₂ (by decide)
  obtain W₂ : Outs (wsOf s) (outs k s) s.mem s₂.mem :=
    (Outside.outs O₁ (own_mem k s) (by omega_using [hsv']) (by omega_using [hsv, hown])).trans
      (Outside.outs O₂ (own_mem k s) (by omega_using []) (by omega_using [hk0]))
  obtain K₁₂ : Keeps [.eax, .esi, .edi, .ebp, .ebx, .ecx, .edx] s s₂ := (K₁.mono (by decide)).widen K₂
  obtain hm : m < 2 ^ (32 * (2 * k)) := by rw [← Nat.mul_assoc]; exact hM.m_lt
  refine csubHead_ok bx₂ (k := k) (src := own k + 4 * (2 * k)) (O := arg s 1)
    (by omega_using [hk0]) hm (by omega_using [htmp]) (by omega_using [hown, htmp]) T₂ (fun t hsp hrd O' => hp.readArg' (i := 1)
      (by rw [hsp, K₂.1 _ (by decide), esp₁]) (by rw [hrd, K₂.2.1, K₁.2.1])
      (W₂.trans (Outside.outs O' (own_mem k s) (by omega_using [htmp]) (by omega_using [hk0, htmp]))) (by decide)) ?_
  intro s₃ K₃ O₃ po₃ b mk₃ S₃ V₃
  obtain bx₃ := bx₂.of_keeps K₃ (by decide)
  obtain W₃ : Outs (wsOf s) (outs k s) s.mem s₃.mem := W₂.trans (Outside.outs O₃ (own_mem k s) (by omega_using [htmp]) (by omega_using [hk0, htmp]))
  -- The save slots are as the entry wrote them.
  obtain sv₃ : ∀ d, saveAt k ≤ d → d + 4 ≤ saveAt k + 16 →
      s₃.mem.readW (off (wsOf s) d) 32 = s₁.mem.readW (off (wsOf s) d) 32 := fun d h1 h2 => by
    rw [Outside.readW32 O₃ (by omega_using [hsv', htmp, h1]) (by omega_using [hown, hsv', h2]), Outside.readW32 O₂ (by omega_using [hsv', h1]) (by omega_using [hown, hsv', h2])]
  simp only [mulRestoreSI, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_bp bx₃ (d := saveAt k + 4) (by omega_using [hown, hsv'])) fun s₄ u₄ _ => ?_
  obtain bx₄ := bx₃.of_keeps u₄.keeps (by decide)
  refine wp_movS (readSrc_bp bx₄ (d := saveAt k + 8) (by omega_using [hown, hsv'])) fun s₅ u₅ _ => ?_
  obtain K₅ : Keeps [.esi, .edi] s₃ s₅ := (u₄.keeps.mono (by decide)).widen u₅.keeps
  obtain bx₅ := bx₃.of_keeps K₅ (by decide)
  obtain mem₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  refine WP.block_append (WP.mono (csubSel_ok bx₅ (by omega_using [hk0]) hm (po₃.of_keeps K₅ (by decide) (by decide))
    (by rw [K₅.1 _ (by decide)]; exact mk₃) (by rw [mem₅]; exact S₃) (by rw [mem₅, V₃]; exact T₂)
    (by omega_using [htmp]) (by omega_using [hown, htmp]) (by omega_arith)) fun s₆ ⟨O₆, V₆, K₆, _⟩ => ?_)
  obtain bx₆ := bx₅.of_keeps K₆ (by decide)
  obtain sv₆ : ∀ d, saveAt k ≤ d → d + 4 ≤ saveAt k + 16 →
      s₆.mem.readW (off (wsOf s) d) 32 = s₁.mem.readW (off (wsOf s) d) 32 := fun d h1 h2 => by
    rw [Outside.readW32 O₆ (by omega_arith) (by omega_using [hown, hsv', h2]), mem₅, sv₃ d h1 h2]
  simp only [restoreBP]
  refine wp_movS (readSrc_bp bx₆ (d := saveAt k) (by omega_using [hown, hsv'])) fun s₇ u₇ _ => ?_
  obtain bx₇ := bx₆.of_keeps u₇.keeps (by decide)
  refine wp_movS (readSrc_bp bx₇ (d := saveAt k + 12) (by omega_using [hown, hsv'])) fun s₈ u₈ _ => WP.block_nil ?_
  obtain mem₈ : s₈.mem = s₆.mem := by rw [u₈.mem, u₇.mem]
  obtain W₈ : Outs (wsOf s) (outs k s) s.mem s₈.mem := by
    rw [mem₈]; exact (W₃.trans (by rw [← mem₅]; exact Outs.refl _ _ _)).trans
      (Outside.outs O₆ (o_mem k s) (by omega_using []) (by omega_using []))
  obtain rv : ∀ {d} {r : Reg}, w32 s₁.mem (wsOf s) d = (s.gpr r).toNat →
      s₁.mem.readW (off (wsOf s) d) 32 = s.gpr r := fun h => BitVec.eq_of_toNat_eq h
  refine ⟨⟨fun r hr => ?_, ?_⟩, W₈, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₈.other _ (by decide), u₇.gpr, sv₆ _ (Nat.le_refl _) (by omega_using []), rv v₁]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), K₆.1 _ (by decide), u₅.other _ (by decide), u₄.gpr,
        sv₃ _ (by omega_using []) (by omega_using []), rv v₂]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), K₆.1 _ (by decide), u₅.gpr, u₄.mem,
        sv₃ _ (by omega_using []) (by omega_using []), rv v₃]
    · rw [u₈.gpr, u₇.mem, sv₆ _ (by omega_using []) (by omega_using []), rv v₄]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), K₆.1 _ (by decide), K₅.1 _ (by decide),
        K₃.1 _ (by decide), K₁₂.1 _ (by decide)]
  · exact (Outs.frame W₈ hp.outs_le).readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ 4)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ret_ws) (by decide)
  · have hT : val32 s₆.mem (wsOf s) (arg s 1).toNat (2 * k) =
        val32 s₂.mem (wsOf s) (own k + 4 * (2 * k)) (2 * k + 1) % m := by
      rw [V₆, mem₅, V₃]
    rw [mem₈, hT]
    refine ⟨Nat.mod_lt _ hM.m_pos, ?_⟩
    obtain hA : val32 s₁.mem (wsOf s) (arg s 2).toNat (2 * k) = val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) :=
      O₁.val32 (by omega_arith) (by omega_using [hown])
    obtain hB' : val32 s₁.mem (wsOf s) (arg s 3).toNat (2 * k) = val32 s.mem (wsOf s) (arg s 3).toNat (2 * k) :=
      O₁.val32 (by omega_using [this, hsv']) (by omega_using [hown])
    rw [hA, hB'] at hU
    rw [Nat.mod_mul_mod, show 64 * k = 32 * (2 * k) by omega_arith, Nat.mul_comm, hU, Nat.add_mul_mod_self_right]

/-! ## The sum and the difference -/

/-- After `asEntry`: `ebp` the working space, `ecx` and `edx` pointing to
`[a]` and `[b]`, the caller's `ebp` saved. -/
theorem asEntry_ok (hp : Pre k s) :
    WP isa (.block (asEntry k)) s fun u =>
      Bx u (wsOf s) 8192 ∧ Ptr u .ecx (arg s 2).toNat ∧ Ptr u .edx (arg s 3).toNat ∧
      Keeps [.eax, .ecx, .edx, .ebp] s u ∧ Outside (wsOf s) (saveAt k + 12) 4 s.mem u.mem ∧
      w32 u.mem (wsOf s) (saveAt k + 12) = (s.gpr .ebp).toNat := by
  have hn := hp.ws_fit
  obtain hws : (wsOf s).toNat = (arg s 0).toNat := by simp only [wsOf, BitVec.toNat_setWidth]; omega_arith
  obtain hn' : (wsOf s).toNat + 8192 ≤ 2 ^ 32 := by rw [hws]; exact hn
  obtain ⟨hsv, -⟩ := saveAt_le hp.k0 hp.k9
  simp only [asEntry]
  refine wp_movS (hp.readArg rfl rfl (Frame.refl _ _) (i := 0) (by decide)) fun s₁ u₁ _ => ?_
  refine wp_storeS (ea_base u₁.gpr hn (d := saveAt k + 12) (by omega_using [hsv]))
    ⟨_, by rw [u₁.wr, hp.wr]; exact List.mem_singleton_self _, Offset.contains_base _ (by omega_using [hsv]) (by omega_using [hsv])⟩
    fun s₂ m₂ => ?_
  obtain hm₂ : s₂.mem = s.mem.writeW (off (wsOf s) (saveAt k + 12)) (s.gpr .ebp) := by
    rw [m₂.mem, u₁.mem, u₁.other .ebp (by decide)]
  obtain O₂ : Outside (wsOf s) (saveAt k + 12) 4 s.mem s₂.mem := by
    rw [hm₂]; exact writeW32_outside _ _ _ (by omega_using [hsv])
  obtain F₂ := Outside.frame O₂ (size := 8192) (by omega_using [hsv])
  obtain esp₂ : s₂.gpr .esp = s.gpr .esp := by rw [m₂.gpr, u₁.other _ (by decide)]
  obtain rd₂ : s₂.rd = s.rd := by rw [m₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [m₂.wr, u₁.wr]
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_movS (hp.readArg (by rw [u₃.other _ (by decide), esp₂]) (by rw [u₃.rd, rd₂])
    (by rw [u₃.mem]; exact F₂) (i := 2) (by decide)) fun s₄ u₄ _ => ?_
  refine wp_addS rfl fun s₅ u₅ _ => ?_
  refine wp_movS (hp.readArg (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₄.rd, u₃.rd, rd₂]) (by rw [u₅.mem, u₄.mem, u₃.mem]; exact F₂) (i := 3) (by decide))
    fun s₆ u₆ _ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => WP.block_nil ?_
  obtain mem₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain ebp₇ : s₇.gpr .ebp = arg s 0 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      m₂.gpr, u₁.gpr]
  obtain hof : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by simp
  obtain bx : Bx s₇ (wsOf s) 8192 := by
    refine ⟨by rw [ebp₇], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, hp.wr]; exact List.mem_singleton_self _, ?_⟩
    exact hn'
  refine ⟨bx, ?_, ?_, ?_, by rw [mem₇]; exact O₂, by rw [mem₇, hm₂, w32_write_self]⟩
  · change s₇.gpr .ecx = s₇.gpr .ebp + _
    rw [ebp₇, hof, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₄.other _ (by decide),
      u₃.gpr, m₂.gpr, u₁.gpr, BitVec.add_comm]
  · change s₇.gpr .edx = s₇.gpr .ebp + _
    rw [ebp₇, hof, u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, m₂.gpr, u₁.gpr, BitVec.add_comm]
  · refine ⟨fun r hr => ?_, by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [u₇.other _ h3, u₆.other _ h3, u₅.other _ h2, u₄.other _ h2, u₃.other _ h4, m₂.gpr, u₁.other _ h1]

/-- `asEntry` and `saveB`. -/
theorem asEntryB_ok (hp : Pre k s) (m : Nat) :
    WP isa (.block (asEntry k ++ saveB k m)) s fun u =>
      Bx u (wsOf s) 8192 ∧ Ptr u .ecx (arg s 2).toNat ∧ Ptr u .edx (arg s 3).toNat ∧
      Keeps [.eax, .ecx, .edx, .ebp] s u ∧ Outside (wsOf s) (saveAt k) 16 s.mem u.mem ∧
      w32 u.mem (wsOf s) (saveAt k + 12) = (s.gpr .ebp).toNat ∧
      (p256Field k m = true → w32 u.mem (wsOf s) (saveAt k) = (s.gpr .ebx).toNat) := by
  have hn := hp.ws_fit
  obtain ⟨hsv, -⟩ := saveAt_le hp.k0 hp.k9
  refine WP.block_append (WP.mono (asEntry_ok hp) fun s₁ ⟨bx, pa, pb, K, O, v⟩ => ?_)
  have O' : Outside (wsOf s) (saveAt k) 16 s.mem s₁.mem := O.mono (by omega_using []) (by omega_using [])
  unfold saveB
  split
  next h =>
    refine wp_storeS (bx.ea (d := saveAt k) (by omega_using [hsv])) (bx.write (by omega_using [hsv])) fun s₂ m₂ =>
      WP.block_nil ?_
    have O₂ : Outside (wsOf s) (saveAt k) 4 s₁.mem s₂.mem := by
      rw [m₂.mem]; exact writeW32_outside _ _ _ (by omega_using [hsv])
    have K₂ : Keeps [] s₁ s₂ := m₂.keeps _
    refine ⟨bx.of_keeps K₂ (by decide), pa.of_keeps K₂ (by decide) (by decide), pb.of_keeps K₂ (by decide) (by decide),
      K.widen K₂ (by decide), O'.trans (O₂.mono (Nat.le_refl _) (by omega_using [])), ?_, fun _ => ?_⟩
    · rw [O₂.w32 (by omega_using []) (by omega_using [hsv]), v]
    · rw [m₂.mem, w32_write_self, K.1 _ (by decide)]
  next h => exact WP.block_nil ⟨bx, pa, pb, K, O', v, fun h' => absurd h' h⟩

theorem chainP_eq (op op' : AluOp) (acc N : Nat) : chainP op op' acc N =
    chainK .eax (fun j => .mem (at_ .ecx (4 * j))) op op' (fun j => .mem (at_ .edx (4 * j)))
      (fun j => bp (acc + 4 * j)) N := rfl

/-- The operands of `chainP`, below `D`. -/
theorem chainP_src {base : Addr} {size : Nat} (hb : Bx s base size) {r : Reg} {p D N : Nat} (hp : Ptr s r p)
    (hr : r ≠ .eax) (hD : p + 4 * N ≤ D) (hDs : D + 4 * N ≤ size) :
    SrcOk (fun j => .mem (at_ r (4 * j))) (fun j => s.mem.readW (off base (p + 4 * j)) 32) .eax base D N s :=
  fun j hj t ht hrd hwr O' => by
    obtain hbt := hb.of_other ht (by decide) hwr
    obtain hpt : Ptr t r p := by change t.gpr r = t.gpr .ebp + _; rw [ht _ hr, ht _ (by decide)]; exact hp
    dsimp only
    rw [readSrc_ptr hbt hpt (d := 4 * j) (by have := hb.nowrap; omega_using [hD, hDs, hj]),
      Outside.readW32 O' (by omega_using [hD, hj]) (by have := hb.nowrap; omega_using [hD, hDs, hj, this])]

/-- `vg_<curve>_add_mod_<p|n>`: `[o] = ([a] + [b]) mod m`. -/
theorem addFn_ok {m : Nat} (hM : MulOk k m) (hp : Pre k s)
    (hab : val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) + val32 s.mem (wsOf s) (arg s 3).toNat (2 * k) < 2 * m) :
    WP isa (addFn k m) s fun u => abiPreserved s u ∧ Outs (wsOf s) (outs k s) s.mem u.mem ∧
      val32 u.mem (wsOf s) (arg s 1).toNat (2 * k) =
        (val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) + val32 s.mem (wsOf s) (arg s 3).toNat (2 * k)) % m := by
  have hk0 := hp.k0
  have ⟨hsv, hown⟩ := saveAt_le hp.k0 hp.k9
  have := hp.fo; have := hp.fa; have := hp.fb
  obtain hsv' : saveAt k = own k + 24 * k + 4 := by simp only [saveAt, tmpAt]; omega_arith
  obtain htmp : tmpAt k = own k + 16 * k + 4 := by simp only [tmpAt]; omega_arith
  simp only [addFn, csubOut, List.append_assoc, List.nil_append, chainP_eq]
  rw [← List.append_assoc (asEntry k)]
  refine WP.block_append (WP.mono (asEntryB_ok hp m) fun s₁ ⟨bx₁, pa₁, pb₁, K₁, O₁, v₁, vb₁⟩ => ?_)
  have hn := bx₁.nowrap
  obtain C := chainKAdd_ok (chainP_src bx₁ pa₁ (by decide) (D := own k) (N := 2 * k)
    (by omega_arith) (by omega_using [hown])) (chainP_src bx₁ pb₁ (by decide) (by omega_using [this]) (by omega_using [hown]))
    (fun j hj t ht hwr => have hbt := bx₁.of_other ht (by decide) hwr; ⟨hbt.ea (by omega_using [hown, hj]), hbt.write (by omega_using [hown, hj])⟩)
    (by omega_using [hown]) (2 * k - 1) (by omega_using [hk0])
  rw [show 2 * k - 1 + 1 = 2 * k by omega_arith] at C
  refine WP.block_append (WP.mono C fun s₂ ⟨O₂, ⟨c, hc, V₂⟩, K₂⟩ => ?_)
  obtain bx₂ := bx₁.of_keeps K₂ (by decide)
  simp only [List.cons_append]
  refine wp_movS rfl fun s₃ u₃ cf₃ => ?_
  refine wp_adcS rfl (by rw [cf₃]; exact hc) fun s₄ u₄ _ => ?_
  obtain K₄ : Keeps [.eax] s₂ s₄ := u₃.keeps.widen u₄.keeps
  obtain bx₄ := bx₂.of_keeps K₄ (by decide)
  refine wp_storeS (bx₄.ea (d := own k + 4 * (2 * k)) (by omega_using [hown])) (bx₄.write (by omega_using [hown])) fun s₅ m₅ => ?_
  obtain K₅ : Keeps [.eax] s₂ s₅ := K₄.trans (m₅.keeps _)
  obtain bx₅ := bx₂.of_keeps K₅ (by decide)
  obtain O₅ : Outside (wsOf s) (own k + 4 * (2 * k)) 4 s₂.mem s₅.mem := by
    rw [m₅.mem, u₄.mem, u₃.mem]; exact writeW32_outside _ _ _ (by omega_using [hown])
  obtain top₅ : w32 s₅.mem (wsOf s) (own k + 4 * (2 * k)) = c.toNat := by
    rw [m₅.mem, w32_write_self, u₄.gpr, u₃.gpr]; cases c <;> rfl
  obtain hA : val32 s₁.mem (wsOf s) (arg s 2).toNat (2 * k) = val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) :=
    O₁.val32 (by omega_arith) (by omega_using [hown])
  obtain hB : val32 s₁.mem (wsOf s) (arg s 3).toNat (2 * k) = val32 s.mem (wsOf s) (arg s 3).toNat (2 * k) :=
    O₁.val32 (by omega_using [this, hsv']) (by omega_using [hown])
  rw [yVal_val32, yVal_val32, hA, hB] at V₂
  obtain T₅ : val32 s₅.mem (wsOf s) (own k) (2 * k + 1) =
      val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) + val32 s.mem (wsOf s) (arg s 3).toNat (2 * k) := by
    rw [val32_succ, top₅, O₅.val32 (by omega_using []) (by omega_using [hown]), ← V₂]
  obtain W₅ : Outs (wsOf s) (outs k s) s.mem s₅.mem :=
    ((Outside.outs O₁ (own_mem k s) (by omega_using [hsv']) (by omega_using [hsv, hown])).trans
      (Outside.outs O₂ (own_mem k s) (by omega_using []) (by omega_using []))).trans
      (Outside.outs O₅ (own_mem k s) (by omega_using []) (by omega_using [hk0]))
  obtain K₁₅ : Keeps [.eax, .ecx, .edx, .ebp] s s₅ := K₁.trans ((K₂.trans K₅).mono (by decide))
  obtain hm : m < 2 ^ (32 * (2 * k)) := by rw [← Nat.mul_assoc]; exact hM.m_lt
  refine csubHead_ok bx₅ (k := k) (src := own k) (O := arg s 1)
    (by omega_using [hk0]) hm (by omega_using [htmp]) (by omega_using [hown, htmp]) (by rw [T₅]; exact hab) (fun t hsp hrd O' => hp.readArg' (i := 1)
      (by rw [hsp, K₁₅.1 _ (by decide)]) (by rw [hrd, K₁₅.2.1])
      (W₅.trans (Outside.outs O' (own_mem k s) (by omega_using [htmp]) (by omega_using [hk0, htmp]))) (by decide)) ?_
  intro s₆ K₆ O₆ po₆ b mk₆ S₆ V₆
  obtain bx₆ := bx₅.of_keeps K₆ (by decide)
  refine WP.block_append (WP.mono (csubSel_ok bx₆ (by omega_using [hk0]) hm po₆ mk₆ S₆ (by rw [V₆, T₅]; exact hab)
    (by omega_using [htmp]) (by omega_using [hown, htmp]) (by omega_arith)) fun s₇ ⟨O₇, V₇, K₇, B₇⟩ => ?_)
  obtain bx₇ := bx₆.of_keeps K₇ (by decide)
  refine WP.mono (restoreP_ok bx₇ (m := m) (by omega_using [hsv])) fun s₈ ⟨M₈, R₈, E₈, B₈⟩ => ?_
  obtain W₈ : Outs (wsOf s) (outs k s) s.mem s₈.mem := by
    rw [M₈]; exact (W₅.trans (Outside.outs O₆ (own_mem k s) (by omega_using [htmp]) (by omega_using [hk0, htmp]))).trans
      (Outside.outs O₇ (o_mem k s) (by omega_using []) (by omega_using []))
  obtain sv : ∀ d, saveAt k ≤ d → d + 4 ≤ saveAt k + 16 →
      w32 s₇.mem (wsOf s) d = w32 s₁.mem (wsOf s) d := fun d h1 h2 => by
    rw [O₇.w32 (by omega_arith) (by omega_using [hown, hsv', h2]),
      O₆.w32 (by omega_using [hsv', htmp, h1]) (by omega_using [hown, hsv', h2]),
      O₅.w32 (by omega_using [hsv', h1]) (by omega_using [hown, hsv', h2]),
      O₂.w32 (by omega_using [hsv', h1]) (by omega_using [hown, hsv', h2])]
  refine ⟨⟨fun r hr => ?_, ?_⟩, W₈, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain K : ∀ r, r ≠ .ebp → r ≠ .ebx → r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₈.gpr r = s.gpr r :=
      fun r h1 h2 h3 h4 h5 => by
        rw [R₈ _ h1 h2, K₇.1 _ (by simp [h5, h2]), K₆.1 _ (by simp [h3, h4]), K₁₅.1 _ (by simp [h1, h3, h4, h5])]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [B₈]
      split
      next h => exact BitVec.eq_of_toNat_eq ((sv _ (Nat.le_refl _) (by omega_using [])).trans (vb₁ h))
      next h => rw [B₇ h, K₆.1 _ (by decide), K₁₅.1 _ (by decide)]
    · exact K _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact K _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [E₈]
      exact BitVec.eq_of_toNat_eq ((sv _ (by omega_using []) (by omega_using [])).trans v₁)
    · exact K _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (Outs.frame W₈ hp.outs_le).readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ 4)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ret_ws) (by decide)
  · rw [M₈, V₇, V₆, T₅]

theorem addOut_eq (src tmp N : Nat) : addOut src tmp N =
    chainK .edx (fun j => .mem (bp (src + 4 * j))) .add .adc (fun j => .mem (bp (tmp + 4 * j)))
      (fun j => at_ .ecx (4 * j)) N := rfl

theorem sub_arith {A B D R m P : Nat} {c c' : Bool} (hA : A < m) (hB : B < m) (hm : m < P) (hR : R < P)
    (hD : D < P) (h1 : D + B = A + P * c.toNat) (h2 : R + P * c'.toNat = D + (if c then m else 0)) :
    R = (A + m - B) % m := by
  obtain key : (R = A + m - B ∧ A < B) ∨ (R = A - B ∧ B ≤ A) := by
    cases c <;> cases c' <;>
      simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Bool.false_eq_true, ite_false,
        ite_true, Nat.add_zero] at h1 h2 <;> omega_arith
  rcases key with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [Nat.mod_eq_of_lt (by omega_using [hB, h])]
  · rw [show A + m - B = (A - B) + m by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [hA])]

/-- `caddOut`: the number at `own`, plus `m` if the mask in `eax` is all ones,
into `[o]`. -/
theorem caddOut_ok {base : Addr} (hb : Bx s base 8192) {k m : Nat} {O : BitVec 32} (hk0 : 0 < k)
    (hown : own k + 64 * k = 4096) (hm : m < 2 ^ (32 * (2 * k))) (ho : O.toNat + 8 * k ≤ own k) {b : Bool}
    (hmk : s.gpr .eax = if b then BitVec.allOnes 32 else 0)
    (hO : ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd = s.rd → Outside base (tmpAt k) (4 * (2 * k)) s.mem t.mem →
      readSrc t (.mem (at_ .esp 8)) = some O) :
    WP isa (.block (caddOut k m)) s fun u =>
      (∃ mem, Outside base (tmpAt k) (4 * (2 * k)) s.mem mem ∧ Outside base O.toNat (4 * (2 * k)) mem u.mem) ∧
      Keeps [.ecx, .edx, .ebx] s u ∧ (¬ p256Field k m = true → u.gpr .ebx = s.gpr .ebx) ∧
      ∃ c : Bool, val32 u.mem base O.toNat (2 * k) + 2 ^ (32 * (2 * k)) * c.toNat =
        val32 s.mem base (own k) (2 * k) + (if b then m else 0) := by
  have hn := hb.nowrap
  have htmp : tmpAt k = own k + 16 * k + 4 := by simp only [tmpAt]; omega_using []
  have ptr : ∀ {t t₁ t₂ : State}, Upd t t₁ .ecx O → Upd t₁ t₂ .ecx (t₁.gpr .ecx + t₁.gpr .ebp) →
      Ptr t₂ .ecx O.toNat := fun {t t₁ t₂} u₁ u₂ => by
    change t₂.gpr .ecx = t₂.gpr .ebp + _
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]
  unfold caddOut
  by_cases hp : p256Field k m = true
  · rw [ite_eq_left hp, List.append_assoc]
    simp only [outPtr, List.cons_append, List.nil_append]
    refine wp_movS (hO s rfl rfl (Outside.refl _ _ _ _)) fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => ?_
    have K₂ : Keeps [.ecx] s s₂ := u₁.keeps.trans u₂.keeps
    have mem₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
    refine WP.mono (maskedAdd_ok (hb.of_keeps K₂ (by decide)) (p256_maskWords hp) (by omega_using [hk0]) hm (ptr u₁ u₂)
      (b := b) (by rw [K₂.1 _ (by decide)]; exact hmk) (src := own k) (by omega_using [hown])
      (by omega_using [ho, hown]) (.inl (by omega_using [ho])))
      fun u ⟨O', K', c, V⟩ => ⟨⟨s.mem, Outside.refl _ _ _ _, by rw [← mem₂]; exact O'⟩,
        (K₂.mono (by decide)).trans (K'.mono (by decide)), fun h => absurd hp h, c, by rw [← mem₂]; exact V⟩
  · rw [ite_eq_right hp, List.append_assoc]
    rw [show maskedI m (tmpAt k) (2 * k) = maskIK m (tmpAt k) (2 * k) from rfl]
    refine WP.block_append (WP.mono (maskIK_ok hb m (tmpAt k) b hmk (2 * k) (by omega_using [hown, htmp]))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    simp only [outPtr, List.cons_append, List.nil_append]
    refine wp_movS (hO s₁ (K₁.1 _ (by decide)) K₁.2.1 O₁) fun s₂ u₂ _ => wp_addS rfl fun s₃ u₃ _ => ?_
    have K₃ : Keeps [.ecx] s₁ s₃ := u₂.keeps.trans u₃.keeps
    have hb₃ := hb₁.of_keeps K₃ (by decide)
    have mem₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
    have po₃ := ptr u₂ u₃
    rw [addOut_eq]
    have C := chainKAdd_ok (s := s₃) (r := .edx) (bp_src hb₃ (p := own k) (D := O.toNat) (N := 2 * k) (by decide)
        (by omega_using [ho]) (by omega_using [hown])) (bp_src hb₃ (p := tmpAt k) (by decide)
        (by omega_using [ho, htmp]) (by omega_using [hown, htmp]))
      (fun j hj t ht hwr => by
        have hbt := hb₃.of_other ht (by decide) hwr
        have hpt : Ptr t .ecx O.toNat := by
          change t.gpr .ecx = t.gpr .ebp + _; rw [ht _ (by decide), ht _ (by decide)]; exact po₃
        exact ⟨hbt.ea_ptr hpt (by omega_using [ho, hown, hj]), hbt.write (by omega_using [ho, hown, hj])⟩)
      (by omega_using [hown, ho]) (2 * k - 1) (by omega_using [hk0])
    rw [show 2 * k - 1 + 1 = 2 * k by omega_using [hk0]] at C
    refine WP.mono C fun u ⟨O', ⟨c, _, V⟩, K'⟩ => ⟨⟨s₁.mem, O₁, by rw [← mem₃]; exact O'⟩,
      ((K₁.mono (by decide)).trans (K₃.mono (by decide))).trans (K'.mono (by decide)), fun _ => ?_, c, ?_⟩
    · rw [K'.1 _ (by decide), K₃.1 _ (by decide), K₁.1 _ (by decide)]
    · rw [yVal_val32, yVal_val32, mem₃, V₁, O₁.val32 (by omega_using [htmp]) (by omega_using [hown, hn]), yVal_mw,
        Nat.mod_eq_of_lt hm] at V
      exact V

/-- `vg_<curve>_sub_mod_<p|n>`: `[o] = ([a] - [b]) mod m`. -/
theorem subFn_ok {m : Nat} (hM : MulOk k m) (hp : Pre k s)
    (ha : val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) < m) (hb : val32 s.mem (wsOf s) (arg s 3).toNat (2 * k) < m) :
    WP isa (subFn k m) s fun u => abiPreserved s u ∧ Outs (wsOf s) (outs k s) s.mem u.mem ∧
      val32 u.mem (wsOf s) (arg s 1).toNat (2 * k) =
        (val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) + m - val32 s.mem (wsOf s) (arg s 3).toNat (2 * k)) % m := by
  have hk0 := hp.k0
  have ⟨hsv, hown⟩ := saveAt_le hp.k0 hp.k9
  have := hp.fo; have := hp.fa; have := hp.fb
  obtain hsv' : saveAt k = own k + 24 * k + 4 := by simp only [saveAt, tmpAt]; omega_arith
  obtain htmp : tmpAt k = own k + 16 * k + 4 := by simp only [tmpAt]; omega_arith
  simp only [subFn, List.append_assoc, chainP_eq]
  rw [← List.append_assoc (asEntry k)]
  refine WP.block_append (WP.mono (asEntryB_ok hp m) fun s₁ ⟨bx₁, pa₁, pb₁, K₁, O₁, v₁, vb₁⟩ => ?_)
  have hn := bx₁.nowrap
  obtain C := chainKSub_ok (chainP_src bx₁ pa₁ (by decide) (D := own k) (N := 2 * k)
    (by omega_arith) (by omega_using [hown])) (chainP_src bx₁ pb₁ (by decide) (by omega_using [this]) (by omega_using [hown]))
    (fun j hj t ht hwr => have hbt := bx₁.of_other ht (by decide) hwr; ⟨hbt.ea (by omega_using [hown, hj]), hbt.write (by omega_using [hown, hj])⟩)
    (by omega_using [hown]) (2 * k - 1) (by omega_using [hk0])
  rw [show 2 * k - 1 + 1 = 2 * k by omega_arith] at C
  refine WP.block_append (WP.mono C fun s₂ ⟨O₂, ⟨c, hc, V₂⟩, K₂⟩ => ?_)
  obtain bx₂ := bx₁.of_keeps K₂ (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_sbbS rfl hc fun s₃ u₃ _ => ?_
  obtain mk₃ : s₃.gpr .eax = if c then BitVec.allOnes 32 else 0 := by
    rw [u₃.gpr, BitVec.sub_self]; cases c <;> decide
  obtain bx₃ := bx₂.of_keeps u₃.keeps (by decide)
  obtain W₃ : Outs (wsOf s) (outs k s) s.mem s₃.mem :=
    ((Outside.outs O₁ (own_mem k s) (by omega_using [hsv']) (by omega_using [hsv, hown])).trans
      (Outside.outs O₂ (own_mem k s) (by omega_using []) (by omega_using []))).trans (by rw [u₃.mem]; exact Outs.refl _ _ _)
  obtain K₁₃ : Keeps [.eax, .ecx, .edx, .ebp] s s₃ := K₁.trans ((K₂.trans u₃.keeps).mono (by decide))
  obtain hm : m < 2 ^ (32 * (2 * k)) := by rw [← Nat.mul_assoc]; exact hM.m_lt
  refine WP.block_append (WP.mono (caddOut_ok bx₃ hk0 hown hm (O := arg s 1) (by omega_arith) mk₃
    (fun t hsp hrd O' => hp.readArg' (i := 1) (by rw [hsp, K₁₃.1 _ (by decide)]) (by rw [hrd, K₁₃.2.1])
      (W₃.trans (Outside.outs O' (own_mem k s) (by omega_using [htmp]) (by omega_using [hk0, htmp]))) (by decide)))
    fun s₇ ⟨⟨mem₄, O₄, O₇⟩, K₇, B₇, c', V₇⟩ => ?_)
  obtain bx₇ := bx₃.of_keeps K₇ (by decide)
  refine WP.mono (restoreP_ok bx₇ (m := m) (by omega_using [hsv])) fun s₈ ⟨M₈, R₈, E₈, B₈⟩ => ?_
  obtain W₈ : Outs (wsOf s) (outs k s) s.mem s₈.mem := by
    rw [M₈]; exact (W₃.trans (Outside.outs O₄ (own_mem k s) (by omega_using [htmp]) (by omega_using [hk0, htmp]))).trans
      (Outside.outs O₇ (o_mem k s) (by omega_using []) (by omega_using []))
  obtain sv : ∀ d, saveAt k ≤ d → d + 4 ≤ saveAt k + 16 →
      w32 s₇.mem (wsOf s) d = w32 s₁.mem (wsOf s) d := fun d h1 h2 => by
    rw [O₇.w32 (by omega_arith) (by omega_using [hown, hsv', h2]),
      O₄.w32 (by omega_using [hsv', htmp, h1]) (by omega_using [hown, hsv', h2]), u₃.mem,
      O₂.w32 (by omega_using [hsv', h1]) (by omega_using [hown, hsv', h2])]
  refine ⟨⟨fun r hr => ?_, ?_⟩, W₈, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain K : ∀ r, r ≠ .ebp → r ≠ .ebx → r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₈.gpr r = s.gpr r :=
      fun r h1 h2 h3 h4 h5 => by
        rw [R₈ _ h1 h2, K₇.1 _ (by simp [h4, h5, h2]), K₁₃.1 _ (by simp [h1, h3, h4, h5])]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [B₈]
      split
      next h => exact BitVec.eq_of_toNat_eq ((sv _ (Nat.le_refl _) (by omega_using [])).trans (vb₁ h))
      next h => rw [B₇ h, K₁₃.1 _ (by decide)]
    · exact K _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact K _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [E₈]
      exact BitVec.eq_of_toNat_eq ((sv _ (by omega_using []) (by omega_using [])).trans v₁)
    · exact K _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (Outs.frame W₈ hp.outs_le).readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ 4)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ret_ws) (by decide)
  · have hA : val32 s₁.mem (wsOf s) (arg s 2).toNat (2 * k) = val32 s.mem (wsOf s) (arg s 2).toNat (2 * k) :=
      O₁.val32 (by omega_arith) (by omega_using [hown])
    obtain hB : val32 s₁.mem (wsOf s) (arg s 3).toNat (2 * k) = val32 s.mem (wsOf s) (arg s 3).toNat (2 * k) :=
      O₁.val32 (by omega_using [this, hsv']) (by omega_using [hown])
    rw [yVal_val32, yVal_val32, hA, hB] at V₂
    rw [M₈]
    rw [u₃.mem] at V₇
    exact sub_arith ha hb hm (val32_lt _ _ _ _) (val32_lt s₂.mem (wsOf s) (own k) (2 * k)) (c := c) (c' := c') V₂ V₇

end VG.Proof.Weierstrass.X86.Mont
