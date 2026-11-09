module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Body
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20 and Poly1305 together (AArch64): the whole chunks

`Stitch.bulk`, from a state with the stream's arguments (`Mixed8.TPre`, the
source at `x1` and the destination at `x4`, with its working space 64 bytes
after the state: `BPre`), at least 512 bytes of data, and the accumulator in
`x21`–`x23`: the chunks that fit encrypted (or decrypted), as the stream's
own chunks (`Mixed8.tbulk_ok`), and the bytes they absorbed: when decrypting,
every chunk's source; when encrypting (in place), the output of every chunk
but the last.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP ChunkedFrom source sr scalarBuf dr TInv TRest
  tcp_of_inv tenter_ok tleave_ok tnext_ok twin_sub zero_batches)
open VG.Proof.ChaCha20.AArch64.Xor (TPre st dp L bp tp stR dR tR bR S0 D0 T0 KS Dst Src)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

theorem WP.both {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁)
    (h₂ : WP isa c s Q₂) : WP isa c s fun u => Q₁ u ∧ Q₂ u := by
  obtain ⟨t₁, u₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, u₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, u₁, e₁, q₁, q₂⟩

/-- The key is apart from what `enterFrom` stores. -/
theorem key_enter {s₀ : State} (hp : BPre s₀) : ∀ r ∈ enterR s₀, (keyR s₀).Disjoint r := by
  have e (d : Nat) : s₀.gpr .x3 + BitVec.ofNat 64 d = st s₀ + BitVec.ofNat 64 (64 + d) := by
    rw [show s₀.gpr .x3 = bp s₀ from rfl, hp.bp, BitVec.add_assoc, ← BitVec.ofNat_add]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [keyR, e] <;>
    exact Offset.disjoint (st s₀) (by decide) (by decide) (by decide)

/-- The key's words in a state with the entry state's `x0`, whose memory
differs from the entry state's only away from the key. -/
theorem rword_eq {s₀ s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hx0 : s.gpr .x0 = s₀.gpr .x0) (hd : ∀ r ∈ rs, (keyR s₀).Disjoint r) :
    ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword s d = Poly.rword s₀ d :=
  rword_of hf hx0 hd

/-- The source the loop has not reached is as on entry. -/
theorem window_orig {s₀ x : State} {t : Nat} (h : TInv s₀ t x) (hge : 512 * t + 512 ≤ L s₀) :
    bytesAt x.mem (dp s₀ + BitVec.ofNat 64 (512 * t)) 512 =
      bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 (512 * t)) 512 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.src _ (by omega_arith) (by omega_arith)]

/-- The destination the loop has passed is the output. -/
theorem prefix_ct {s₀ : State} {m : Mem} {t n : Nat} (h : Dst s₀ (512 * t) m) (hle : 512 * t ≤ L s₀)
    (hn : n ≤ 512 * t) :
    bytesAt m (tp s₀) n = (List.range n).map fun k => D0 s₀ k ^^^ (KS s₀).getD k 0 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [h _ (by omega_arith), ite_eq_left (by omega_arith)]

theorem bytesAt_join (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n ++ bytesAt m (p + BitVec.ofNat 64 n) 512 = bytesAt m p (n + 512) :=
  (Poly1305.bytesAt_add m p n 512).symm

theorem absorb_join {R a : Nat} {X Y : List Byte} (hx : X.length % 16 = 0) :
    absorbAll R (absorbAll R a X) Y = absorbAll R a (X ++ Y) :=
  (Poly1305.absorbAll_append hx).symm

theorem eval_zero5 {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 512 then 1 else 0)) :
    isa.eval (.zero .x .x5) s = some (decide (512 ≤ n)) := zero_batches h

/-- The loop of chunks that decrypt. -/
theorem chunks_open {s₀ : State} (hp : BPre s₀) {R a : Nat} {s : State} {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) (h : TInv (rebase s₀ s) t s)
    (ha : Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * t))) s) :
    WP isa (chunks sve false) s fun u => ∃ T, L s₀ - 512 * T < 512 ∧ t < T ∧
      TInv (rebase s₀ u) T u ∧ Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * T))) u := by
  let Inv : Nat → State → Prop := fun n x => ∃ i, n = L s₀ - 512 * i ∧ 512 ≤ n ∧ t ≤ i ∧
    TInv (rebase s₀ x) i x ∧ Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * i))) x
  refine WP.loop (M := isa) Inv ?_ (L s₀ - 512 * t) s ⟨t, rfl, by omega_arith, Nat.le_refl _, h, ha⟩
  rintro n x ⟨i, rfl, hge', hti, hx, hax⟩
  have hb : dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i) =
      dataOf false (dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i)) := by
    simp only [dataOf, Bool.false_eq_true, ite_false, BitVec.add_zero]
  refine (body_ok false (hp.rebase x) (fun h => nomatch h) (t := i) (by simp; omega_arith) hx (w := 512 * i)
    (by simp; omega_arith) hb hax).mono fun v ⟨⟨hv, h5⟩, hav⟩ => ?_
  rw [rebase_rebase] at hv
  have hwin := window_orig hx (by simp; omega_arith)
  simp only [dp_rebase, rebase_mem] at hwin hav
  rw [hwin, absorb_join (by rw [Poly1305.length_bytesAt]; omega_arith), bytesAt_join,
    show 512 * i + 512 = 512 * (i + 1) by omega_arith] at hav
  rw [L_rebase] at h5
  have hc := eval_zero5 h5
  by_cases he : L s₀ - 512 * (i + 1) < 512
  · left
    rw [decide_eq_false (show ¬ 512 ≤ L s₀ - 512 * (i + 1) by omega_arith)] at hc
    exact ⟨hc, i + 1, he, by omega_arith, hv, hav⟩
  · right
    rw [decide_eq_true (show 512 ≤ L s₀ - 512 * (i + 1) by omega_arith)] at hc
    exact ⟨hc, L s₀ - 512 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by omega_arith, hv, hav⟩

/-- The loop of chunks that encrypt in place, each absorbing the output of the
one before. -/
theorem chunks_seal {s₀ : State} (hp : BPre s₀) (hin : tp s₀ = dp s₀) {R a : Nat} {s : State} {t : Nat}
    (ht : 1 ≤ t) (hge : 512 * t + 512 ≤ L s₀) (h : TInv (rebase s₀ s) t s)
    (ha : Acc R (absorbAll R a (bytesAt s.mem (dp s₀) (512 * (t - 1)))) s) :
    WP isa (chunks sve true) s fun u => ∃ T, L s₀ - 512 * T < 512 ∧ t < T ∧
      TInv (rebase s₀ u) T u ∧
      Acc R (absorbAll R a (bytesAt u.mem (dp s₀) (512 * (T - 1)))) u := by
  let Inv : Nat → State → Prop := fun n x => ∃ i, n = L s₀ - 512 * i ∧ 512 ≤ n ∧ t ≤ i ∧
    TInv (rebase s₀ x) i x ∧ Acc R (absorbAll R a (bytesAt x.mem (dp s₀) (512 * (i - 1)))) x
  refine WP.loop (M := isa) Inv ?_ (L s₀ - 512 * t) s ⟨t, rfl, by omega_arith, Nat.le_refl _, h, ha⟩
  rintro n x ⟨i, rfl, hge', hti, hx, hax⟩
  have hb : dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i) =
      dataOf true (dp (rebase s₀ x) + BitVec.ofNat 64 (512 * (i - 1))) := by
    simp only [dataOf, ite_true, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_arith
  refine (body_ok true (hp.rebase x) (fun _ => by simpa using hin) (t := i) (by simp; omega_arith) hx
    (w := 512 * (i - 1)) (by simp; omega_arith) hb hax).mono fun v ⟨⟨hv, h5⟩, hav⟩ => ?_
  rw [rebase_rebase] at hv
  simp only [dp_rebase] at hav
  rw [absorb_join (by rw [Poly1305.length_bytesAt]; omega_arith), bytesAt_join,
    show 512 * (i - 1) + 512 = 512 * (i + 1 - 1) by omega_arith] at hav
  have p1 := prefix_ct hx.data hx.le (n := 512 * (i + 1 - 1)) (by omega_arith)
  have p2 := prefix_ct hv.data hv.le (n := 512 * (i + 1 - 1)) (by omega_arith)
  simp only [tp_rebase, D0_rebase, KS_rebase, hin] at p1 p2
  rw [p1, ← p2] at hav
  rw [L_rebase] at h5
  have hc := eval_zero5 h5
  by_cases he : L s₀ - 512 * (i + 1) < 512
  · left
    rw [decide_eq_false (show ¬ 512 ≤ L s₀ - 512 * (i + 1) by omega_arith)] at hc
    exact ⟨hc, i + 1, he, by omega_arith, hv, hav⟩
  · right
    rw [decide_eq_true (show 512 ≤ L s₀ - 512 * (i + 1) by omega_arith)] at hc
    exact ⟨hc, L s₀ - 512 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by omega_arith, hv, hav⟩

/-- `leaveFrom` only loads (and moves). -/
theorem leave_mem (s : State)
    (hi : ∀ d n, d + n ≤ 320 → InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.leaveFrom) s fun u => u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self,
    VG.Impl.ChaCha20.AArch64.Mixed8.leaveFrom, VG.Impl.ChaCha20.AArch64.Mixed8.savedFrom,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, runBlock_cons,
    runBlock_nil, exec, addr, Size.bytes, Size.bits, State.load, State.read,
    hi 128 16 (by decide), hi 144 16 (by decide), hi 256 8 (by decide), hi 264 8 (by decide),
    hi 272 8 (by decide), hi 280 8 (by decide), RegUpd.gpr_write, BitVec.setWidth_eq,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, State.setV, Option.bind_some, Option.map_some, isa,
    runStep_some, Option.some.injEq, exists_eq_left']

theorem rebase_self {s₀ u : State} (h : ∀ r ∈ accRegs, u.gpr r = s₀.gpr r) : rebase s₀ u = s₀ := by
  simp only [rebase]
  cases s₀
  congr 1
  funext r
  by_cases hr : r ∈ accRegs <;> simp only [hr, ite_true, ite_false, h r]

/-- What the bulk leaves: `T` chunks done, and the bytes absorbed. -/
structure Bulked (enc : Bool) (R a : Nat) (s₀ : State) (T : Nat) (u : State) : Prop where
  pos : 1 ≤ T
  rest : L s₀ - 512 * T < 512
  inv : TRest (rebase s₀ u) T u
  acc : Acc R (absorbAll R a (if enc then bytesAt u.mem (dp s₀) (512 * (T - 1))
    else bytesAt s₀.mem (dp s₀) (512 * T))) u

/-- Leaving, after the chunks. -/
theorem leave_bulk {enc : Bool} {s₀ : State} (hp : BPre s₀) {R a : Nat} {u : State} {T : Nat}
    (hT : 1 ≤ T) (hr : L s₀ - 512 * T < 512) (h : TInv (rebase s₀ u) T u)
    (ha : Acc R (absorbAll R a (if enc then bytesAt u.mem (dp s₀) (512 * (T - 1))
      else bytesAt s₀.mem (dp s₀) (512 * T))) u) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.leaveFrom) u (Bulked enc R a s₀ T) := by
  have hi : ∀ d n, d + n ≤ 320 → InRegions (u.rd ++ u.wr) (u.gpr .x3 + BitVec.ofNat 64 d) n := by
    intro d n hd
    rw [h.rd, h.wr, h.x3]
    simp only [rebase_rd, rebase_wr, bp_rebase, hp.rd, hp.wr]
    exact ⟨bR s₀, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  refine (WP.both (tleave_ok (hp.rebase u).toTPre h) (leave_mem u hi)).mono
    fun v ⟨hl, hm⟩ => ?_
  have hacc : ∀ r ∈ accRegs, v.gpr r = u.gpr r := fun r hr =>
    (hl.cs r (acc_preserved r hr).1).trans (rebase_acc hr)
  have e := rebase_congr s₀ hacc
  refine ⟨hT, hr, e ▸ hl, ?_⟩
  rw [hm]
  exact ha.frame (acc_regs_keep hacc) fun d _ => by
    simp only [Poly.rword, hm, hl.x0, h.x0]

theorem bytesAt_zero (m : Mem) (p : Addr) : bytesAt m p 0 = [] := rfl

theorem bulk_ok (enc : Bool) {s₀ : State} (hp : BPre s₀) (hin : enc = true → tp s₀ = dp s₀)
    (hL : 512 ≤ L s₀) {R a : Nat} (ha : Acc R a s₀) :
    WP isa (bulk sve enc) s₀ fun u => ∃ T, Bulked enc R a s₀ T u := by
  have ho : ∀ d n, d + n ≤ 320 → InRegions s₀.wr (s₀.gpr .x3 + BitVec.ofNat 64 d) n := by
    intro d n hd
    rw [hp.wr]
    exact ⟨bR s₀, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have nil (m : Mem) (k : Nat) (hk : k = 0) :
      absorbAll R a (bytesAt m (dp s₀) (512 * k)) = a := by
    rw [hk, Nat.mul_zero, bytesAt_zero, Poly1305.absorbAll_nil]
  unfold bulk
  apply WP.seq
  refine (WP.both (tenter_ok hp.toTPre (fun _ _ => rfl) rfl rfl rfl rfl rfl) (enter_frame s₀ ho)).mono
    fun s₁ ⟨h₁, f₁⟩ => ?_
  have acc₁ : ∀ r ∈ accRegs, s₁.gpr r = s₀.gpr r := fun r hr =>
    h₁.cs r (acc_preserved r hr).1 (acc_preserved r hr).2.1 (acc_preserved r hr).2.2.2
      (by intro he; rw [he] at hr; exact absurd hr (by decide)) (acc_preserved r hr).2.2.1
  have rw₁ := rword_eq f₁ h₁.x0 (key_enter hp)
  have ha₁ : Acc R a s₁ := ha.frame (acc_regs_keep acc₁) rw₁
  have hb₁ : TInv (rebase s₀ s₁) 0 s₁ := by rw [rebase_self acc₁]; exact h₁
  apply WP.seq
  cases enc
  · -- Decrypting: every chunk absorbs its source.
    simp only [Bool.false_eq_true, ite_false]
    refine (chunks_open hp (R := R) (a := a) (t := 0) (by omega_arith) hb₁
      (by rw [nil _ _ rfl]; exact ha₁)).mono fun u ⟨T, hr, hT, hu, hau⟩ => ?_
    exact (leave_bulk (enc := false) hp (by omega_arith) hr hu (by simpa using hau)).mono
      fun w hw => ⟨T, hw⟩
  · -- Encrypting: the first chunk is the kernel's.
    have hin' := hin rfl
    simp only [ite_true]
    apply WP.seq
    obtain ⟨hcp, hsrc⟩ := tcp_of_inv hp.toTPre h₁ (by omega_arith)
    have hbody : WP isa (VG.Impl.ChaCha20.AArch64.Mixed8.bodyFrom sve) s₁ fun v => ∃ g,
        ChunkedFrom .x27 s₁ g ∧ TInv s₀ (0 + 1) v ∧
        v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (0 + 1) < 512 then 1 else 0) ∧
        Frame [stR s₀] g.mem v.mem :=
      WP.seq ((VG.Proof.ChaCha20.AArch64.Mixed8.chunkFrom_ok .x27 s₁ hcp hsrc).mono fun g hg =>
        (tnext_ok hp.toTPre (t := 0) (by omega_arith) h₁ hg).mono fun v ⟨hv, h5, hf⟩ => ⟨g, hg, hv, h5, hf⟩)
    refine hbody.mono fun v ⟨g, hg, hv, h5, hf⟩ => ?_
    have accv : ∀ r ∈ accRegs, v.gpr r = s₀.gpr r := fun r hr =>
      hv.cs r (acc_preserved r hr).1 (acc_preserved r hr).2.1 (acc_preserved r hr).2.2.2
        (by intro he; rw [he] at hr; exact absurd hr (by decide)) (acc_preserved r hr).2.2.1
    have hfv : Frame (enterR s₀ ++ [sr s₁, scalarBuf s₁, dr s₁] ++ [stR s₀]) s₀.mem v.mem :=
      ((f₁.mono (by simp)).trans (hg.frame.mono (by simp))).trans (hf.mono (by simp))
    have hx0v : v.gpr .x0 = s₀.gpr .x0 := hv.x0
    have rwv := rword_eq hfv hx0v (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · exact key_enter hp r hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · simpa only [sr, h₁.x0] using hp.st_b.symm.sub_left hp.key_sub
          · simp only [keyR, scalarBuf, h₁.x3, hp.bp]
            exact Offset.disjoint (st s₀) (d := 224) (n := 16) (e := 64) (k := 128) (by decide)
              (by decide) (by decide)
          · simp only [dr, h₁.x1]
            exact (hp.t_b.symm.sub_left hp.key_sub).sub_right (twin_sub (by omega_arith))
      · rw [List.mem_singleton.mp hr]; exact (hp.st_b.symm.sub_left hp.key_sub))
    have hav : Acc R (absorbAll R a (bytesAt v.mem (dp s₀) (512 * (1 - 1)))) v := by
      rw [nil _ _ rfl]; exact ha.frame (acc_regs_keep accv) rwv
    have hbv : TInv (rebase s₀ v) 1 v := by rw [rebase_self accv]; exact hv
    apply WP.ite (decide (L s₀ - 512 * (0 + 1) < 512))
      (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short h5)
    · intro hs
      have hs' := of_decide_eq_true hs
      exact WP.block_nil ((leave_bulk (enc := true) hp (Nat.le_refl 1) (by omega_arith) hbv
        (by simpa using hav)).mono fun w hw => ⟨1, hw⟩)
    · intro hs
      have hs' := of_decide_eq_false hs
      refine (chunks_seal hp hin' (t := 1) (Nat.le_refl 1) (by omega_arith) hbv hav).mono
        fun u ⟨T, hr, hT, hu, hau⟩ => ?_
      exact (leave_bulk (enc := true) hp (by omega_arith) hr hu (by simpa using hau)).mono
        fun w hw => ⟨T, hw⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch
