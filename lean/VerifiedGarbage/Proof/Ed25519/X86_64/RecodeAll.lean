import VerifiedGarbage.Proof.Ed25519.X86_64.RecodeLoop
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits

/-!
# Both scalars' digits on x86-64

`recodeAll` zeroes the digits' array (bytes 2048–3103), copies `k` (64 bytes, from the pointer at
byte 7952) to byte 3104 and `S` (32 bytes, from the pointer at byte 7944, plus 32) to byte 3176,
each followed by eight zero bytes, recodes them (`recode_ok`), `k`'s `c` bytes with windows of
five bits into the even bytes of the array and `S`'s with windows of eight bits into the odd ones,
and sets the counter to `8c + 9` (`recodeAll_ok`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519.Recode
open VG.Proof.X25519.X86_64 (off ofs Keeps)
open VG.Impl.X25519.X86_64 (sc at_)

/-! ## Stores into the scratch -/

theorem writeW_byte {m : Mem} {a x : Addr} (v : BitVec 64) :
    m.writeW a v x = if (x - a).toNat < 8 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  simp only [Mem.writeW, Mem.write]
  rfl

/-- Byte `t < 8` of a word read from `b` and written at `a`. -/
theorem writeW_readW_byte (m m' : Mem) (a b : Addr) {t : Nat} (ht : t < 8) :
    m.writeW a (m'.readW b 64) (a + BitVec.ofNat 64 t) = m' (b + BitVec.ofNat 64 t) := by
  rw [writeW_byte, Mem.sub_ofNat_toNat a (by omega), ite_eq_left ht]
  simp only [Mem.readW]
  exact Mem.extractLsb'_read m' b ht

/-- The bytes of the scratch from `d` to `d + n` hold `f`, the rest is as in `m`. -/
def Holds (base : Addr) (d n : Nat) (f : Nat → Byte) (m m' : Mem) : Prop :=
  (∀ j < n, m' (off base (d + j)) = f j) ∧
    ∀ x, (ofs base x < d ∨ d + n ≤ ofs base x) → m' x = m x

theorem storeSc_ok {s : State} {base : Addr} (hs : Scratch s base) (d : Nat) (hd : d + 8 ≤ 8192)
    (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hw : InRegions s.wr (off base d) 8 := ⟨_, hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- A word of `0`s stored at `d`. -/
theorem zeroWord {m : Mem} {base : Addr} {d : Nat}
    (hd : d + 8 ≤ 8192) (x : Addr) :
    m.writeW (off base d) (0 : BitVec 64) x =
      if d ≤ ofs base x ∧ ofs base x < d + 8 then 0 else m x := by
  have e := Offset.lt_iff x base (d := d) (n := 8) (by omega)
  rw [writeW_byte]
  by_cases h : (x - off base d).toNat < 8
  · rw [ite_eq_left h, ite_eq_left (e.mp h)]; simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (e.mpr h'))]

theorem zeroPrefix_ok {s : State} {base : Addr} (hs : Scratch s base) (hz : s.gpr .rax = 0)
    (n : Nat) (hn : n ≤ 132) :
    WP isa (.block ((List.range n).map fun j => .store (sc (2048 + 8 * j)) .rax)) s fun t =>
      Holds base 2048 (8 * n) (fun _ => 0) s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  induction n with
  | zero => exact WP.block_nil ⟨⟨fun j hj => by omega, fun _ _ => rfl⟩, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun a ⟨⟨ah, ao⟩, ag, ar, aw⟩ => ?_
    have ha : Scratch a base := ⟨by rw [ag]; exact hs.rdi, aw ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (storeSc_ok ha (2048 + 8 * n) (by omega) .rax) fun t ⟨tm, tg, tr, tw⟩ => ?_
    have hb := hs.nowrap
    refine ⟨⟨fun j hj => ?_, fun x hx => ?_⟩, tg.trans ag, tr.trans ar, tw.trans aw⟩
    · rw [tm, ag, hz, zeroWord (by omega), VG.Proof.X25519.X86_64.ofs_off' base (by omega)]
      split
      · rfl
      · exact ah j (by omega)
    · rw [tm, ag, hz, zeroWord (by omega), ite_eq_right (by omega), ao x (by omega)]

/-- The digits' array zeroed. -/
theorem zeroDigits_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block zeroDigits) s fun t =>
      Holds base 2048 1056 (fun _ => 0) s.mem t.mem ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
        t.gpr .rax = 0 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [zeroDigits, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rax (.imm 0)]) s fun t =>
      t.gpr .rax = 0 ∧ Keeps [.rax] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun a ⟨az, ka⟩ => ?_
  refine WP.mono (zeroPrefix_ok (hs.of_keeps ka (by decide)) az 132 (Nat.le_refl _))
    fun t ⟨th, tg, tr, tw⟩ => ?_
  refine ⟨⟨th.1, fun x hx => by rw [th.2 x hx, ka.2.1]⟩, fun r hr => by rw [tg, ka.1 r (by simpa using hr)],
    by rw [tg, az], tr.trans ka.2.2.1, tw.trans ka.2.2.2⟩

/-! ## The scalars' copies -/

theorem copyPair_ok {s : State} {base P : Addr} (hs : Scratch s base) (hP : s.gpr .rsi = P) (o d : Nat)
    (hd : d + 8 ≤ 8192) (hr : InRegions (s.rd ++ s.wr) (off P o) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsi o)), .store (sc d) .rax]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.mem.readW (off P o) 64) ∧
        (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hw : InRegions s.wr (off base d) 8 := ⟨_, hs.wr, Offset.contains_base _ hd (by omega)⟩
  have hea : s.ea (at_ .rsi o) = off P o := by
    simp only [State.ea, at_, hP, BitVec.ofInt_natCast]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.store64, hea,
    VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, hs.rdi, hr, hw, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, trivial, trivial⟩
  simp only [hr, ite_false]

theorem copyPrefix_ok {s : State} {base P : Addr} (hs : Scratch s base) (hP : s.gpr .rsi = P)
    (o d : Nat) (n : Nat) (hd : d + 8 * n ≤ 8192)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (off P (o + 8 * j)) 8)
    (hf : ∀ j < 8 * n, 8192 ≤ ofs base (off P (o + j))) :
    WP isa (.block ((List.range n).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (o + 8 * j))), .store (sc (d + 8 * j)) .rax])) s fun t =>
      Holds base d (8 * n) (fun j => s.mem (off P (o + j))) s.mem t.mem ∧
        (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  induction n with
  | zero => exact WP.block_nil ⟨⟨fun j hj => by omega, fun _ _ => rfl⟩, fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega) (fun j hj => hr j (by omega)) (fun j hj => hf j (by omega)))
      fun a ⟨⟨ah, ao⟩, ag, ar, aw⟩ => ?_
    have ha : Scratch a base := ⟨by rw [ag _ (by decide)]; exact hs.rdi, aw ▸ hs.wr, hs.nowrap⟩
    have hsrc : ∀ t < 8, a.mem (off P (o + 8 * n) + BitVec.ofNat 64 t) = s.mem (off P (o + (8 * n + t))) := by
      intro t ht
      have h1 := hf (8 * n + t) (by omega)
      rw [Offset.add_add, show o + 8 * n + t = o + (8 * n + t) by omega]
      exact ao _ (Or.inr (by simp only [off] at h1 ⊢; omega))
    refine WP.mono (copyPair_ok ha (P := P) (by rw [ag _ (by decide)]; exact hP) (o + 8 * n) (d + 8 * n) (by omega)
      (by rw [ar, aw]; exact hr n (by omega))) fun t ⟨tm, tg, tr, tw⟩ => ?_
    have hb := hs.nowrap
    refine ⟨⟨fun j hj => ?_, fun x hx => ?_⟩, fun r hr' => (tg r hr').trans (ag r hr'), tr.trans ar, tw.trans aw⟩
    · rw [tm]
      by_cases hjn : j < 8 * n
      · rw [writeW_byte, ite_eq_right ?_, ah j hjn]
        rw [Offset.lt_iff _ base (by omega), Mem.sub_ofNat_toNat base (by omega)]
        omega
      · have e : off base (d + j) = off base (d + 8 * n) + BitVec.ofNat 64 (j - 8 * n) := by
          rw [Offset.add_add, show d + 8 * n + (j - 8 * n) = d + j by omega]
        rw [e, writeW_readW_byte _ _ _ _ (by omega), hsrc _ (by omega)]
        congr 2; omega
    · rw [tm, writeW_byte, ite_eq_right ?_, ao x (by omega)]
      rw [Offset.lt_iff x base (by omega)]
      simp only [ofs] at hx
      omega

theorem leNum_leBytes_mod (n x : Nat) :
    Proof.X25519.leNum (Proof.X25519.leBytes n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [Proof.X25519.leBytes, Proof.X25519.leNum]; omega
  | succ n ih =>
    rw [Proof.X25519.leBytes_succ, Proof.X25519.leNum, ih, BitVec.toNat_ofNat,
      show 256 ^ (n + 1) = 256 * 256 ^ n by rw [Nat.pow_succ, Nat.mul_comm], Nat.mod_mul]

/-- Bytes of `X` from `src` make it `Copied`. -/
theorem copied_of_bytes {m : Mem} {base : Addr} {src N X : Nat}
    (h : ∀ j < N, m (off base (src + j)) = BitVec.ofNat 8 (X / 256 ^ j)) {nb : Nat} (hnb : nb + 8 ≤ N) :
    Copied m base src nb X := by
  intro b hb
  rw [← Proof.X25519.leNum_bytesAt_64]
  have e : Spec.X25519.bytesAt m (off base (src + b)) 8 = Proof.X25519.leBytes 8 (X / 256 ^ b) := by
    simp only [Spec.X25519.bytesAt, Proof.X25519.leBytes]
    apply List.map_congr_left
    intro i hi
    have hi8 := List.mem_range.mp hi
    rw [Offset.add_add, show src + b + i = src + (b + i) by omega, h (b + i) (by omega),
      Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [e, leNum_leBytes_mod, show 256 ^ b = 2 ^ (8 * b) by rw [Nat.pow_mul],
    show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]

/-- `X`'s bytes from `p`, as numbers. -/
theorem input_ofNat (m : Mem) (p : Addr) {n j : Nat} (hj : j < n) :
    m (off p j) = BitVec.ofNat 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, show 2 ^ 8 = 256 from rfl, decodeLE_byte, input_byte m p n j hj]

theorem past_ofNat (m : Mem) (p : Addr) {n j : Nat} (hj : n ≤ j) :
    (0 : Byte) = BitVec.ofNat 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ j) := by
  have hl := decodeLE_lt (Spec.Ed25519.bytesAt m p n)
  have hlen : (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]
  rw [hlen] at hl
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hl (Nat.pow_le_pow_right (by decide) hj))]
  rfl

theorem loadSc_ok {s : State} {base : Addr} (hs : Scratch s base) (r : Reg) (d : Nat)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hr, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hk)

/-- `k`'s and `S`'s bytes copied, each followed by eight zero bytes. -/
theorem copyScalars_ok {s : State} {base kp sp : Addr} (hs : Scratch s base)
    (hkp : s.mem.readW (off base 7952) 64 = kp) (hsp : s.mem.readW (off base 7944) 64 = sp)
    (hkr : ∀ j < 8, InRegions (s.rd ++ s.wr) (off kp (8 * j)) 8)
    (hsr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sp (32 + 8 * j)) 8)
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j))
    (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j))) :
    WP isa (.block copyScalars) s fun t =>
      (∀ j < 72, t.mem (off base (3104 + j)) =
        BitVec.ofNat 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ j)) ∧
      (∀ j < 40, t.mem (off base (3176 + j)) =
        BitVec.ofNat 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ j)) ∧
      (∀ x, (ofs base x < 3104 ∨ 3216 ≤ ofs base x) → t.mem x = s.mem x) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hb := hs.nowrap
  rw [show copyScalars = [.mov .rsi (.mem (sc 7952))] ++ (((List.range 8).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (0 + 8 * j))), .store (sc (3104 + 8 * j)) .rax]) ++
      ([.mov .rsi (.mem (sc 7944))] ++ (((List.range 4).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (32 + 8 * j))), .store (sc (3176 + 8 * j)) .rax]) ++
      ([.mov32 .rax (.imm 0)] ++ ([.store (sc 3168) .rax] ++ [.store (sc 3208) .rax]))))) by
    simp only [copyScalars, Nat.zero_add, List.append_assoc, List.cons_append, List.nil_append]]
  rw [WP.block_append_iff]
  refine WP.mono (loadSc_ok hs .rsi 7952 (by decide)) fun a ⟨ap, ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyPrefix_ok ha (P := kp) (by rw [ap, hkp]) 0 3104 8 (by decide)
    (fun j hj => by rw [ka.2.2.1, ka.2.2.2]; simpa using hkr j hj)
    (fun j hj => by simpa using hkf j hj)) fun b ⟨⟨bh, bo⟩, bg, br, bw⟩ => ?_
  have hsb : Scratch b base := ⟨by rw [bg _ (by decide), ka.1 _ (by decide)]; exact hs.rdi, bw ▸ ha.wr, hb⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadSc_ok hsb .rsi 7944 (by decide)) fun c ⟨cp, kc⟩ => ?_
  have hc := hsb.of_keeps kc (by decide)
  have csp : c.gpr .rsi = sp := by
    rw [cp, ← hsp, ← ka.2.1]
    exact Mem.readW_congr fun i hi => bo _ (Or.inr (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))
  have hfar : ∀ j < 32, b.mem (off sp (32 + j)) = s.mem (off sp (32 + j)) := fun j hj =>
    (bo _ (Or.inr (by have := hsf j hj; omega))).trans (by rw [ka.2.1])
  rw [WP.block_append_iff]
  refine WP.mono (copyPrefix_ok hc (P := sp) csp 32 3176 4 (by decide)
    (fun j hj => by rw [kc.2.2.1, kc.2.2.2, br, bw, ka.2.2.1, ka.2.2.2]; exact hsr j hj)
    (fun j hj => hsf j hj)) fun d ⟨⟨dh, d_o⟩, dg, dr, dw⟩ => ?_
  have hsd : Scratch d base :=
    ⟨by rw [dg _ (by decide), kc.1 _ (by decide), bg _ (by decide), ka.1 _ (by decide)]; exact hs.rdi,
      dw ▸ hc.wr, hb⟩
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rax (.imm 0)]) d fun t =>
      t.gpr .rax = 0 ∧ Keeps [.rax] d t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun e ⟨ez, ke⟩ => ?_
  have he := hsd.of_keeps ke (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeSc_ok he 3168 (by decide) .rax) fun f ⟨fm, fg, fr, fw⟩ => ?_
  have hf : Scratch f base := ⟨by rw [fg]; exact he.rdi, fw ▸ he.wr, hb⟩
  refine WP.mono (storeSc_ok hf 3208 (by decide) .rax) fun t ⟨tm, tg, tr, tw⟩ => ?_
  -- What each piece of memory holds.
  have z1 := zeroWord (m := e.mem) (base := base) (d := 3168) (by decide)
  have z2 := zeroWord (m := f.mem) (base := base) (d := 3208) (by decide)
  rw [ez] at fm
  rw [fg, ez] at tm
  have hmem : ∀ x, t.mem x = if 3208 ≤ ofs base x ∧ ofs base x < 3216 then 0 else
      if 3168 ≤ ofs base x ∧ ofs base x < 3176 then 0 else d.mem x := by
    intro x; rw [tm, z2, fm, z1, ke.2.1]
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun x hx => ?_, fun r hr hs' => ?_, ?_, ?_⟩
  · rw [hmem, VG.Proof.X25519.X86_64.ofs_off' base (by omega)]
    by_cases h64 : j < 64
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        d_o _ (Or.inl (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)), kc.2.1,
        bh j (by omega)]
      simp only [Nat.zero_add, ka.2.1]
      exact input_ofNat s.mem kp h64
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), past_ofNat s.mem kp (n := 64) (j := j) (by omega)]
  · rw [hmem, VG.Proof.X25519.X86_64.ofs_off' base (by omega)]
    by_cases h32 : j < 32
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), dh j (by omega)]
      simp only [kc.2.1]
      rw [hfar j h32, show off sp (32 + j) = off (off sp 32) j from (Offset.add_add _ _ _).symm]
      exact input_ofNat s.mem (off sp 32) h32
    · rw [ite_eq_left (by omega), past_ofNat s.mem (off sp 32) (n := 32) (j := j) (by omega)]
  · rw [hmem, ite_eq_right (by omega), ite_eq_right (by omega), d_o x (by omega), kc.2.1,
      bo x (by omega), ka.2.1]
  · rw [tg, fg, ke.1 r (by simpa using hr), dg r hr, kc.1 r (by simpa using hs'), bg r hr,
      ka.1 r (by simpa using hs')]
  · rw [tr, fr, ke.2.2.1, dr, kc.2.2.1, br, ka.2.2.1]
  · rw [tw, fw, ke.2.2.2, dw, kc.2.2.2, bw, ka.2.2.2]

/-! ## The bounds and the counter -/

theorem boundS_spec (s₀ : State) (base : Addr) (dst : Nat) : BoundSpec s₀ base dst 32 boundS := by
  intro t _ i hi hi1
  have hcf : (BitVec.ofNat 64 i).toNat < ((256 : BitVec 32).signExtend 64).toNat ↔ i < 8 * 32 := by
    rw [show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 256 from rfl, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [boundS, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.cf_arithFlags, hi, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  rw [decide_eq_decide.mpr hcf]

theorem boundK_spec {s₀ : State} {base : Addr} (hs : Scratch s₀ base) {c : Nat} (hc64 : c ≤ 64)
    (hc : s₀.mem.readW (off base 56) 64 = BitVec.ofNat 64 c) (dst : Nat) :
    BoundSpec s₀ base dst c boundK := by
  intro t kt i hi hi1
  have ht := kt.scratch hs
  have tc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 c := by
    rw [← hc]
    exact Mem.readW_congr fun j hj => kt.mem _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))
  have hr : InRegions (t.rd ++ t.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ ht.wr, Offset.contains_base _ (by decide) (by omega)⟩
  have hshl : BitVec.ofNat 64 c <<< 3 = BitVec.ofNat 64 (8 * c) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have hcf : (BitVec.ofNat 64 i).toNat < (BitVec.ofNat 64 (8 * c)).toNat ↔ i < 8 * c := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [boundK, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift,
    State.load64, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.cf_arithFlags, ht.rdi, hr, tc, hshl, hi, show 1 ≤ 3 ∧ 3 ≤ 63 by decide, and_self,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rw [decide_eq_decide.mpr hcf], fun r hr => ?_, ?_, ?_, ?_⟩
  · have hr' : r ≠ .rax := by simpa using hr
    simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr', ite_false]
  all_goals simp only [RegUpd.mem_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
    RegUpd.rd_arithFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.wr_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags]

theorem setTop_ok {s : State} {base : Addr} (hs : Scratch s base) {c : Nat}
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c) :
    WP isa (.block setTop) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (8 * c + 9) ∧
      (∀ x, (ofs base x < 56 ∨ 64 ≤ ofs base x) → t.mem x = s.mem x) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by omega)⟩
  have hw : InRegions s.wr (off base 56) 8 := ⟨_, hs.wr, Offset.contains_base _ (by decide) (by omega)⟩
  have hshl : BitVec.ofNat 64 c <<< 3 = BitVec.ofNat 64 (8 * c) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have hadd : BitVec.ofNat 64 (8 * c) + (9 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (8 * c + 9) := by
    rw [show (9 : BitVec 32).signExtend 64 = BitVec.ofNat 64 9 from rfl, BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [setTop, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift,
    State.load64, State.store64, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.mem_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.rd_arithFlags, hs.rdi, hr, hw, hc, hshl, hadd, show 1 ≤ 3 ∧ 3 ≤ 63 by decide, and_self,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨Mem.readW_writeW_self64 _ _ _, fun x hx => ?_, fun r hr => ?_, trivial⟩
  · exact VG.Proof.X25519.X86_64.writeW_outside s.mem base _ (by decide) x (by omega)
  · simp only [hr, ite_false]

/-! ## Both scalars -/

/-- What `recodeAll` may change: its registers, the counter and bytes 2048–3215. -/
structure AllKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ recRegs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : ∀ x, (ofs base x < 56 ∨ (64 ≤ ofs base x ∧ ofs base x < 2048) ∨ 3216 ≤ ofs base x) →
    t.mem x = s.mem x

/-- The digits' array zeroed and the scalars copied. -/
structure Copies (base : Addr) (c K S : Nat) (b : State) : Prop where
  scratch : Scratch b base
  counter : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  cK : Copied b.mem base 3104 c K
  cS : Copied b.mem base 3176 32 S
  zero : ∀ dst < 2, ∀ j < 528, dig b.mem base dst j = 0

theorem recodeCopy_ok {s : State} {base kp sp : Addr} (hs : Scratch s base) {c : Nat}
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c) (hc64 : c ≤ 64)
    (hkp : s.mem.readW (off base 7952) 64 = kp) (hsp : s.mem.readW (off base 7944) 64 = sp)
    (hkr : ∀ j < 8, InRegions (s.rd ++ s.wr) (off kp (8 * j)) 8)
    (hsr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sp (32 + 8 * j)) 8)
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j))
    (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j))) :
    WP isa (.block (zeroDigits ++ copyScalars)) s fun b =>
      Copies base c (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32)) b ∧
      (∀ x, (ofs base x < 2048 ∨ 3216 ≤ ofs base x) → b.mem x = s.mem x) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → b.gpr r = s.gpr r) ∧ b.rd = s.rd ∧ b.wr = s.wr := by
  have hb := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (zeroDigits_ok hs) fun a ⟨⟨ah, ao⟩, ag, _, ar, aw⟩ => ?_
  have ha : Scratch a base := ⟨by rw [ag _ (by decide)]; exact hs.rdi, aw ▸ hs.wr, hb⟩
  have aread (d : Nat) (hd : d + 8 ≤ 2048) : a.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
    Mem.readW_congr fun i hi => ao _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))
  have aread' (d : Nat) (hd : 3104 ≤ d) (hd' : d + 8 ≤ 8192) :
      a.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
    Mem.readW_congr fun i hi => ao _ (Or.inr (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))
  have afar (x : Addr) (hx : 8192 ≤ ofs base x) : a.mem x = s.mem x := ao x (Or.inr (by omega))
  refine WP.mono (copyScalars_ok ha (by rw [aread' 7952 (by decide) (by decide)]; exact hkp)
    (by rw [aread' 7944 (by decide) (by decide)]; exact hsp)
    (fun j hj => by rw [ar, aw]; exact hkr j hj) (fun j hj => by rw [ar, aw]; exact hsr j hj)
    hkf hsf) fun b ⟨bK, bS, bo, bg, br, bw⟩ => ?_
  -- The scalars, from `a`'s bytes, are `s`'s.
  have eK : Spec.Ed25519.bytesAt a.mem kp 64 = Spec.Ed25519.bytesAt s.mem kp 64 := by
    simp only [Spec.Ed25519.bytesAt]
    exact List.map_congr_left fun j hj => afar _ (hkf j (List.mem_range.mp hj))
  have eS : Spec.Ed25519.bytesAt a.mem (off sp 32) 32 = Spec.Ed25519.bytesAt s.mem (off sp 32) 32 := by
    simp only [Spec.Ed25519.bytesAt]
    exact List.map_congr_left fun j hj => afar _ (by
      rw [Offset.add_add]; exact hsf j (List.mem_range.mp hj))
  rw [eK] at bK
  rw [eS] at bS
  have hsb : Scratch b base :=
    ⟨by rw [bg _ (by decide) (by decide), ag _ (by decide)]; exact hs.rdi, bw ▸ ha.wr, hb⟩
  have bc : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 c := by
    rw [← hc, ← aread 56 (by decide)]
    exact Mem.readW_congr fun i hi => bo _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))
  have bz : ∀ dst < 2, ∀ j < 528, dig b.mem base dst j = 0 := by
    intro dst hd j hj
    simp only [dig]
    rw [bo _ (Or.inl (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)),
      show 2048 + 2 * j + dst = 2048 + (2 * j + dst) by omega, ah _ (by omega)]
    rfl
  refine ⟨⟨hsb, bc, copied_of_bytes bK (by omega), copied_of_bytes bS (by decide), bz⟩,
    fun x hx => by rw [bo x (by omega), ao x (by omega)], fun r hr hs' => by rw [bg r hr hs', ag r hr],
    by rw [br, ar], by rw [bw, aw]⟩

theorem recodeAll_ok {s : State} {base kp sp : Addr} (hs : Scratch s base) {c : Nat}
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c) (hc32 : 32 ≤ c) (hc64 : c ≤ 64)
    (hkp : s.mem.readW (off base 7952) 64 = kp) (hsp : s.mem.readW (off base 7944) 64 = sp)
    (hkr : ∀ j < 8, InRegions (s.rd ++ s.wr) (off kp (8 * j)) 8)
    (hsr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sp (32 + 8 * j)) 8)
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j))
    (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j))) :
    WP isa recodeAll s fun t =>
      (∀ j < 528, dig t.mem base 0 j =
        digits 5 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64)) (8 * c) j) ∧
      (∀ j < 528, dig t.mem base 1 j =
        digits 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32)) (8 * 32) j) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (8 * c + 9) ∧ AllKeep base s t := by
  rw [recodeAll]
  refine WP.seq (WP.mono (recodeCopy_ok hs hc hc64 hkp hsp hkr hsr hkf hsf)
    fun b ⟨⟨hsb, bc, cK, cS, bz⟩, bo, bg, br, bw⟩ => ?_)
  generalize Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K at cK ⊢
  generalize Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S at cS ⊢
  -- `k`'s digits.
  refine WP.seq (WP.mono (recode_ok hsb (by decide) (by decide) (by decide) (by omega) cK (by omega)
    (boundK_spec hsb hc64 bc 0) (bz 0 (by decide))) fun d ⟨dK, kd⟩ => ?_)
  have hsd := kd.scratch hsb
  have cS' : Copied d.mem base 3176 32 S := cS.of_keep (by decide) (by decide) fun x hx => kd.mem x (by omega)
  refine WP.seq (WP.mono (recode_ok hsd (by decide) (by decide) (by decide) (by decide) cS' (by decide)
    (boundS_spec d base 1) (fun j hj => by
      simp only [dig]
      rw [kd.mem _ (Or.inr (Or.inr (by
        rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)))]
      exact bz 1 (by decide) j hj)) fun e ⟨eS', ke⟩ => ?_)
  have hse := ke.scratch hsd
  have ec : e.mem.readW (off base 56) 64 = BitVec.ofNat 64 c := by
    rw [← bc]
    exact Mem.readW_congr fun i hi => (ke.mem _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))).trans (kd.mem _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega)))
  refine WP.mono (setTop_ok hse ec) fun t ⟨tc, tm, tg, tr, tw⟩ => ?_
  refine ⟨fun j hj => ?_, fun j hj => ?_, tc, ⟨fun r hr => ?_, ?_, ?_, fun x hx => ?_⟩⟩
  · simp only [dig]
    rw [tm _ (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)),
      ke.mem _ (Or.inr (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)))]
    exact dK j hj
  · simp only [dig]
    rw [tm _ (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)]; omega))]
    exact eS' j hj
  · rw [tg r (fun e => hr (by rw [e]; decide)), ke.gpr r hr, kd.gpr r hr,
      bg r (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide))]
  · rw [tr, ke.rd, kd.rd, br]
  · rw [tw, ke.wr, kd.wr, bw]
  · rw [tm x (by omega), ke.mem x (by omega), kd.mem x (by omega), bo x (by omega)]

end VG.Proof.Ed25519.X86_64
