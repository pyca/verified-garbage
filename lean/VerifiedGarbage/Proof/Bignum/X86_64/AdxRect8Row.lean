import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.Rectangular

/-! ## AdxRect8Embed -/
section

/-! Embed a local tile update in the full raw product without subtraction. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

/-- Unchanged words before and after the tile cancel from the value equation. -/
theorem embed {m m' : Mem} {B : Addr} {e d n : Nat} {extra : List (Nat × Nat)}
    (hn : d+16 ≤ n) (hZ : e+8*n ≤ (2 : Nat)^64) (hc : ∀ r ∈ extra, r.1+r.2 ≤ e)
    (hf : Frm B ((e+8*d,128)::extra) m m') :
    wv m' B e n + (2 : Nat)^(64*d)*wv m B (e+8*d) 16 =
      wv m B e n + (2 : Nat)^(64*d)*wv m' B (e+8*d) 16 := by
  have lo : wv m' B e d = wv m B e d := hf.wv_eq (by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp only []; omega
    · have := hc r hr; omega) (by omega)
  have hi : wv m' B (e+8*(d+16)) (n-(d+16)) = wv m B (e+8*(d+16)) (n-(d+16)) :=
    hf.wv_eq (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp only []; omega
      · have := hc r hr; omega) (by omega)
  have shape : n = d+(16+(n-(d+16))) := by omega
  rw [shape,wv_add,wv_add,wv_add,wv_add]
  rw [show e+8*d+8*16 = e+8*(d+16) by omega,lo,hi]
  simp only [show 64*16=1024 from rfl]
  generalize (2 : Nat)^1024 = Q
  exact (VG.Proof.Bignum.Rectangular.surround (A := wv m B e d) (P := (2 : Nat)^(64*d))
    (X := wv m B (e+8*d) 16) (X' := wv m' B (e+8*d) 16)
    (Q := Q) (Y := wv m B (e+8*(d+16)) (n-(d+16))))

/-- A tile's carry equation extends to the whole raw product. -/
theorem embed_value {m m' : Mem} {B : Addr} {e d n u v cin cout q r : Nat} {extra : List (Nat × Nat)}
    (hn : d+16 ≤ n) (hZ : e+8*n ≤ (2 : Nat)^64) (hc : ∀ r ∈ extra, r.1+r.2 ≤ e)
    (hf : Frm B ((e+8*d,128)::extra) m m')
    (ht : wv m' B (e+8*d) 16 + q*cout =
      wv m B (e+8*d) 16 + u*v + r*cin) :
    wv m' B e n + (2 : Nat)^(64*d)*q*cout =
      wv m B e n + (2 : Nat)^(64*d)*(u*v) + (2 : Nat)^(64*d)*r*cin := by
  have eq := embed hn hZ hc hf
  exact VG.Proof.Bignum.Rectangular.lift_value eq ht

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8RowInv -/
section

/-! The invariant keeps the full product plus its pending row carry exact. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

def rawBase (w : Nat) := slot w aAcc+16

def rowRanges (w : Nat) : List (Nat × Nat) :=
  [(rawBase w,16*w),(carryOffset,8),(8*sFn 13,8)]

structure RowInv (s₀ : State) (B : Addr) (Z w a b i j₀ k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  indexI : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i
  indexJ : word s.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k)
  carry : (word s.mem B carryOffset).toNat ≤ 1
  keep : Keep mmRegs s₀ s
  frame : Frm B (rowRanges w) s₀.mem s.mem
  endPtr : k=0 ∨ s.gpr .rsi = off B (rawBase w+8*(i+j₀+8*k))
  val : wv s.mem B (rawBase w) (2*w) +
      (2 : Nat)^(64*(i+j₀+8*(k+1))) * (word s.mem B carryOffset).toNat =
    wv s₀.mem B (rawBase w) (2*w) +
      (2 : Nat)^(64*(i+j₀)) * wv s₀.mem B (slot w a+8*i) 8 * wv s₀.mem B (slot w b+8*j₀) (8*k)

/-- Input arrays remain disjoint from the entire raw product and its counters. -/
theorem input_preserved {m m' : Mem} {B : Addr} {w a i n : Nat}
    (ha : a < 8) (h1 : a ≠ aAcc) (h2 : a ≠ aTmp) (hi : i+n ≤ w)
    (hZ : slot w 8 ≤ (2 : Nat)^64) (hf : Frm B (rowRanges w) m m') :
    wv m' B (slot w a+8*i) n = wv m B (slot w a+8*i) n := by
  have sa := slot_le (w := w) ha
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  apply hf.wv_eq
  · intro r hr
    simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [] <;>
      simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc,aTmp] at * <;> omega
  · omega

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Stream -/
section

/-! The row's loop keeps the eight output words at `d` in the columns. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols cols_keep)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

/-- The raw product with the columns as its eight words at `d`. -/
def streamVal (s : State) (B : Addr) (w d : Nat) : Nat :=
  wv s.mem B (rawBase w) d + 2^(64*d) * cols s +
    2^(64*(d+8)) * wv s.mem B (rawBase w+8*(d+8)) (2*w-(d+8))

structure StreamInv (s₀ : State) (B : Addr) (Z w a b i j₀ k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  indexI : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i
  indexJ : word s.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k)
  carry : (word s.mem B carryOffset).toNat ≤ 1
  keep : Keep mmRegs s₀ s
  frame : Frm B (rowRanges w) s₀.mem s.mem
  pa : s.gpr .rcx = off B (slot w a+8*i)
  pb : s.gpr .rbp = off B (slot w b+8*(j₀+8*k))
  po : s.gpr .rsi = off B (rawBase w+8*(i+j₀+8*k))
  val : streamVal s B w (i+j₀+8*k) +
      (2 : Nat)^(64*(i+j₀+8*(k+1))) * (word s.mem B carryOffset).toNat =
    wv s₀.mem B (rawBase w) (2*w) +
      (2 : Nat)^(64*(i+j₀)) * wv s₀.mem B (slot w a+8*i) 8 * wv s₀.mem B (slot w b+8*j₀) (8*k)

private theorem stream_arith {L Lo Cs Ct U H A Yb Bk W Q T R cs ct P : Nat}
    (hP : P = Q*T)
    (htile : Lo + R*Ct + R*R*ct = Cs + R*U + A*Bk + R*cs)
    (hinv : L + P*Cs + P*R*(U+R*H) + P*R*cs = W + Q*A*Yb) :
    (L + P*Lo) + P*R*Ct + P*R*R*H + P*R*R*ct = W + Q*A*(Yb + T*Bk) := by
  have e1 : P*(Lo + R*Ct + R*R*ct) = P*(Cs + R*U + A*Bk + R*cs) := by rw [htile]
  subst hP
  grind

/-- The value with the columns equal to the memory's eight words at `d`. -/
theorem streamVal_eq {s : State} {B : Addr} {w d : Nat} (hd : d+8 ≤ 2*w)
    (hc : cols s = wv s.mem B (rawBase w+8*d) 8) :
    streamVal s B w d = wv s.mem B (rawBase w) (2*w) := by
  unfold streamVal
  rw [hc,show 2*w = d+(8+(2*w-(d+8))) by omega,wv_add,wv_add,
    show rawBase w+8*d+8*8 = rawBase w+8*(d+8) by omega,show d+(8+(2*w-(d+8)))-(d+8) = 2*w-(d+8) by omega,
    show 64*(d+8) = 64*d+64*8 by omega,Nat.pow_add]
  generalize (2 : Nat)^(64*d) = P
  generalize (2 : Nat)^(64*8) = R
  grind

theorem streamStep_inv {s₀ s : State} {B : Addr} {Z w a b i j₀ k n : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : w < (2 : Nat)^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hn : w = j₀+8*n) (hk : k < n)
    (h : StreamInv s₀ B Z w a b i j₀ k mi s) :
    WP isa AdxRect8.rowStep s fun t =>
      t.zf = some (decide (k+1=n)) ∧ StreamInv s₀ B Z w a b i j₀ (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega
  have hj : j₀+8*k+8 ≤ w := by omega
  have ar := tile_ranges hi hj ha ha1 ha2
  have br := tile_ranges hj hi hb hb1 hb2
  have rt := slot_le (w := w) (show aTmp < 8 by decide)
  have rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega
  -- the tile's output words, after the header, the carry slot and the column index
  have eOdef : rawBase w+8*(i+j₀+8*k) = slot w aAcc+16+8*(i+(j₀+8*k)) := by unfold rawBase; omega
  have po : s.gpr .rsi = off B (slot w aAcc+16+8*(i+(j₀+8*k))) := by rw [← eOdef]; exact h.po
  have prev := h.val
  generalize hd : i+j₀+8*k = d at *
  generalize he : rawBase w+8*d = e at *
  have hdw : d+16 ≤ 2*w := by omega
  have eH : hdrBytes ≤ e := by rw [← he]; unfold rawBase slot; omega
  have eC : carryOffset+8 ≤ e := by rw [← he]; unfold rawBase carryOffset sFn slot hdrBytes aAcc; omega
  have eJ : 8*sFn 13+8 ≤ e := by rw [← he]; unfold rawBase sFn slot hdrBytes aAcc; omega
  have eI : 8*sFn 12+8 ≤ e := by rw [← he]; unfold rawBase sFn slot hdrBytes aAcc; omega
  have eR : rawBase w ≤ e ∧ e+128 ≤ rawBase w+8*(2*w) := by rw [← he]; omega
  have cJ : 8*sFn 13+8 ≤ carryOffset ∨ carryOffset+8 ≤ 8*sFn 13 := by unfold carryOffset sFn; omega
  have cI : 8*sFn 12+8 ≤ carryOffset ∨ carryOffset+8 ≤ 8*sFn 12 := by unfold carryOffset sFn; omega
  unfold AdxRect8.rowStep
  refine WP.seq (WP.mono (streamTile_ok h.scr h.rdi h.pa h.pb po (by omega) (by omega) (by omega)
    ar.2.2 (by omega) (by rw [← eOdef]; exact eC)) fun u ⟨eq,_,one,fr,pu,bu,ku⟩ => ?_)
  rw [← eOdef] at fr eq pu
  have fr3 : Frm B [(e,64),(carryOffset,8),(8*sFn 13,8)] s.mem u.mem := fr.mono (by simp)
  have hu : Hdr u.mem B w mi := frame_hdr h.hdr eH fr3
  have ju : word u.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k) := by
    rw [fr.word_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl eJ
      · exact cJ) (by unfold sFn; omega)]
    exact h.indexJ
  have iu : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [fr.word_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl eI
      · exact cI) (by unfold sFn; omega)]
    exact h.indexI
  refine WP.mono (nextColumn_ok (h.scr.congr ku.2.2) ((ku.gpr (by decide)).trans h.rdi)
    hu hZ (by omega) (by omega) ju) fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside B (8*sFn 13) 8 u.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by unfold sFn; omega)
  have toU : Frm B (rowRanges w) s.mem u.mem := by
    intro x hx
    apply fr x
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    have a0 := hx (rawBase w,16*w) (by simp [rowRanges])
    have a1 := hx (carryOffset,8) (by simp [rowRanges])
    rcases hr with rfl | rfl
    · simp only [] at a0 ⊢; omega
    · exact a1
  have wider : Frm B (rowRanges w) s.mem t.mem := toU.trans (Frm.of_outside ot (by simp [rowRanges]))
  have va := input_preserved ha ha1 ha2 hi Z64 h.frame
  have vb := input_preserved hb hb1 hb2 hj Z64 h.frame
  have ct : word t.mem B carryOffset = word u.mem B carryOffset :=
    ot.word cJ.symm (by omega)
  have colsT : cols t = cols u := cols_keep kt (by decide)
  refine ⟨?_,⟨h.scr.congr (ku.trans kt).2.2,frame_hdr (n := 64) hu eH (Frm.of_outside ot (by simp)),
    (kt.gpr (by decide)).trans ((ku.gpr (by decide)).trans h.rdi),?_,?_,by rw [ct]; exact one h.carry,
    (h.keep.trans (ku.trans kt)).mono (by decide),h.frame.trans wider,
    (kt.gpr (by decide)).trans ((ku.gpr (by decide)).trans h.pa),?_,?_,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [ot.word (by unfold sFn; omega) (by unfold sFn; omega)]; exact iu
  · rw [mt,word_writeW_self,show j₀+8*(k+1) = j₀+8*k+8 by omega]
  · rw [kt.gpr (by decide),bu]
    exact congrArg (off B) (by omega)
  · rw [kt.gpr (by decide),pu,show i+j₀+8*(k+1) = d+8 by omega,← he]
    exact congrArg (off B) (by omega)
  · have below : wv t.mem B (rawBase w) d = wv s.mem B (rawBase w) d := by
      rw [ot.wv (by unfold rawBase slot sFn hdrBytes aAcc; omega) (by omega)]
      exact fr.wv_eq (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact Or.inl (by simp only []; omega)
        · exact Or.inr (by simp only []; unfold rawBase slot hdrBytes aAcc carryOffset sFn; omega)) (by omega)
    have above : wv t.mem B (e+128) (2*w-(d+16)) = wv s.mem B (e+128) (2*w-(d+16)) := by
      rw [ot.wv (by omega) (by omega)]
      exact fr.wv_eq (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact Or.inr (by simp only []; omega)
        · exact Or.inr (by simp only []; omega)) (by omega)
    have upper : wv u.mem B (e+64) 8 = wv s.mem B (e+64) 8 := by
      exact fr.wv_eq (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact Or.inr (by simp only []; omega)
        · exact Or.inr (by simp only []; omega)) (by omega)
    have lowT : wv t.mem B e 8 = wv u.mem B e 8 := ot.wv (by omega) (by omega)
    have hsplit : streamVal s B w d = wv s.mem B (rawBase w) d + 2^(64*d) * cols s +
        2^(64*d) * 2^512 * (wv s.mem B (e+64) 8 + 2^512 * wv s.mem B (e+128) (2*w-(d+16))) := by
      unfold streamVal
      rw [show 2*w-(d+8) = 8+(2*w-(d+16)) by omega,wv_add,
        show rawBase w+8*(d+8) = e+64 by omega,show e+64+8*8 = e+128 by omega,
        show 64*(d+8) = 64*d+512 by omega,Nat.pow_add,show (64 : Nat)*8 = 512 from rfl]
    have tsplit : streamVal t B w (d+8) = (wv s.mem B (rawBase w) d +
          2^(64*d) * wv u.mem B e 8) + 2^(64*d) * 2^512 * cols u +
        2^(64*d) * 2^512 * 2^512 * wv s.mem B (e+128) (2*w-(d+16)) := by
      unfold streamVal
      rw [wv_add,below,he,lowT,colsT,show rawBase w+8*(d+8+8) = e+128 by omega,
        show 2*w-(d+8+8) = 2*w-(d+16) by omega,above,
        show 64*(d+8) = 64*d+512 by omega,show 64*(d+8+8) = 64*d+512+512 by omega,
        Nat.pow_add,Nat.pow_add,Nat.pow_add]
    have bk : wv s₀.mem B (slot w b+8*j₀) (8*(k+1)) = wv s₀.mem B (slot w b+8*j₀) (8*k) +
        2^(64*(8*k)) * wv s.mem B (slot w b+8*(j₀+8*k)) 8 := by
      rw [show 8*(k+1) = 8*k+8 by omega,wv_add,show slot w b+8*j₀+8*(8*k) = slot w b+8*(j₀+8*k) by omega,vb]
    rw [show i+j₀+8*(k+1) = d+8 by omega,show i+j₀+8*(k+1+1) = d+8+8 by omega,ct,bk,tsplit,
      show 64*(d+8+8) = 64*d+512+512 by omega,Nat.pow_add,Nat.pow_add]
    rw [show i+j₀+8*(k+1) = d+8 by omega,hsplit,show 64*(d+8) = 64*d+512 by omega,Nat.pow_add] at prev
    rw [va] at eq
    have hPQ : (2 : Nat)^(64*d) = 2^(64*(i+j₀)) * 2^(64*(8*k)) := by
      rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
    generalize (2 : Nat)^512 = R at eq prev ⊢
    generalize (2 : Nat)^(64*d) = P at hPQ prev ⊢
    exact stream_arith hPQ eq prev

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Row -/
section

/-! Correctness and termination of a complete rectangular row. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols cols_keep)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

/-- The row's columns loaded, after `setup`: the loop's state before its first
column block, for any `s₀` with `u`'s memory and registers but those `setup`
sets. -/
theorem rowLoad_ok {s₀ u : State} {B : Addr} {Z w a b i j₀ : Nat} {mi : BitVec 64}
    (hs : Scr u B Z) (hd : u.gpr .rdi = B) (hh : Hdr u.mem B w mi) (hZ : slot w 8 ≤ Z) (hi : i+8 ≤ w)
    (hj : j₀+8 ≤ w)
    (hidx : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word u.mem B (8*sFn 13) = BitVec.ofNat 64 j₀)
    (hc : (word u.mem B carryOffset).toNat = 0)
    (ua : u.gpr .rcx = off B (slot w a+8*i)) (ub : u.gpr .rbp = off B (slot w b+8*j₀))
    (uo : u.gpr .rsi = off B (slot w aAcc+16+8*(i+j₀)))
    (hm : u.mem = s₀.mem) (hk : Keep mmRegs s₀ u) :
    WP isa (.block AdxRotate8.loadCols) u (StreamInv s₀ B Z w a b i j₀ 0 mi) := by
  have nowrap := hs.nowrap
  have rt := slot_le (w := w) (show aTmp < 8 by decide)
  have rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega
  have uo' : u.gpr .rsi = off B (rawBase w+8*(i+j₀+8*0)) := by
    rw [uo]; exact congrArg (off B) (by unfold rawBase; omega)
  refine WP.mono (AdxRotate8.loadCols_ok hs uo' (by omega)) fun v ⟨cv,kv⟩ => ?_
  have mv : v.mem = u.mem := kv.2.1
  exact ⟨hs.congr kv.2.2.2,mv ▸ hh,(kv.1 .rdi (by decide)).trans hd,mv ▸ hidx,
    by simpa only [Nat.mul_zero,Nat.add_zero,mv] using hjdx,by rw [mv,hc]; omega,
    (hk.trans kv.keep).mono (by decide),by rw [mv,hm]; exact Frm.refl _ _ _,
    (kv.1 .rcx (by decide)).trans ua,by rw [kv.1 .rbp (by decide),ub]; simp only [Nat.mul_zero,Nat.add_zero],
    (kv.1 .rsi (by decide)).trans uo',by
      rw [streamVal_eq (by omega) (by rw [cv,mv]),mv,hc,hm]
      simp only [Nat.mul_zero,Nat.add_zero,wv]⟩

/-- The columns stored after the loop's last column block. -/
theorem rowEnd_ok {s₀ t : State} {B : Addr} {Z w a b i j₀ n : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hi : i+8 ≤ w) (hwN : w = j₀+8*n)
    (ht : StreamInv s₀ B Z w a b i j₀ n mi t) :
    WP isa (.block AdxRotate8.storeCols) t (RowInv s₀ B Z w a b i j₀ n mi) := by
  have rt := slot_le (w := w) (show aTmp < 8 by decide)
  have rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega
  have tnow := ht.scr.nowrap
  have hDw : i+j₀+8*n+8 ≤ 2*w := by omega
  have oI : 8*sFn 12+8 ≤ rawBase w+8*(i+j₀+8*n) := by unfold rawBase sFn slot hdrBytes aAcc; omega
  have oJ : 8*sFn 13+8 ≤ rawBase w+8*(i+j₀+8*n) := by unfold rawBase sFn slot hdrBytes aAcc; omega
  have oC : carryOffset+8 ≤ rawBase w+8*(i+j₀+8*n) := by
    unfold rawBase carryOffset sFn slot hdrBytes aAcc; omega
  have oH : hdrBytes ≤ rawBase w+8*(i+j₀+8*n) := by unfold rawBase slot; omega
  have small : 8*sFn 13+8 ≤ 2^64 ∧ 8*sFn 12+8 ≤ 2^64 ∧ carryOffset+8 ≤ 2^64 := by
    unfold carryOffset sFn; omega
  refine WP.mono (AdxRotate8.storeCols_ok ht.scr ht.po (by omega)) fun x ⟨vx,ox,kx⟩ => ?_
  have fx : Frm B (rowRanges w) t.mem x.mem := by
    intro y hy
    apply ox y
    have a0 := hy (rawBase w,16*w) (by simp [rowRanges])
    simp only [] at a0 ⊢
    omega
  refine ⟨ht.scr.congr kx.2.2,ht.hdr.of_outside ox oH,
    (kx.gpr (by simp)).trans ht.rdi,?_,?_,?_,(ht.keep.trans kx).mono (by simp),ht.frame.trans fx,
    Or.inr ((kx.gpr (by simp)).trans ht.po),?_⟩
  · rw [ox.word (Or.inl oI) small.2.1]; exact ht.indexI
  · rw [ox.word (Or.inl oJ) small.1]; exact ht.indexJ
  · rw [ox.word (Or.inl oC) small.2.2]; exact ht.carry
  · have val := ht.val
    rw [ox.word (Or.inl oC) small.2.2]
    have same : streamVal x B w (i+j₀+8*n) = streamVal t B w (i+j₀+8*n) := by
      unfold streamVal
      rw [cols_keep kx (by decide),ox.wv (Or.inl (by omega)) (by omega),ox.wv (Or.inr (by omega)) (by omega)]
    rw [← streamVal_eq hDw (by rw [cols_keep kx (by decide),vx]),same]
    exact val


theorem row_ok {s : State} {B : Addr} {Z w a b i j₀ n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hwN : w = j₀+8*n) (hn : 0 < n)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j₀)
    (hc : (word s.mem B carryOffset).toNat = 0) :
    WP isa (AdxRect8.row ca cb) s (RowInv s B Z w a b i j₀ n mi) := by
  unfold AdxRect8.row
  refine WP.seq (WP.mono (setup_ok hs hd hh hZ hv pa pb hidx hjdx) fun u ⟨ua,ub,uo,um,ku⟩ => ?_)
  refine WP.seq (WP.mono (rowLoad_ok (s₀ := s) (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd) (um ▸ hh) hZ hi
    (by omega) (um ▸ hidx) (um ▸ hjdx) (um ▸ hc) ua ub uo um (ku.mono (by decide))) fun v hv0 => ?_)
  exact WP.seq (WP.mono (wp_upto (a := 0) (N := n) (Q := StreamInv s B Z w a b i j₀ n mi) hn
    (StreamInv s B Z w a b i j₀ · mi)
    (fun _ _ hk _ h => streamStep_inv hZ hw hi ha hb ha1 ha2 hb1 hb2 hwN hk h)
    (fun _ h => h) hv0) fun t ht => rowEnd_ok hZ hi hwN ht)

end VG.Proof.Bignum.X86_64.AdxRect8

end
