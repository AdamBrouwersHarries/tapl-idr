module OTP

data Bit : Type where
  ZeroBit : Bit
  OneBit : Bit

data BitVector : Nat -> Type where
  Nil : BitVector Z
  Cons : Bit -> BitVector n -> BitVector (S n)
%name BitVector xs,ys

-- this represents the empty bit vector
emptyBitVect : BitVector Z
emptyBitVect = Nil

-- this represents the bits 101
aBitVect : BitVector 3
aBitVect = Cons OneBit (Cons ZeroBit (Cons OneBit Nil))

-- this represents the bits 110
anotherBitVect : BitVector 3
anotherBitVect = Cons OneBit (Cons OneBit (Cons ZeroBit Nil))


-- xor between two individual bits.
xor : Bit -> Bit -> Bit
xor ZeroBit ZeroBit = ZeroBit
xor ZeroBit OneBit = OneBit
xor OneBit ZeroBit = OneBit
xor OneBit OneBit = ZeroBit

-- xor between two bit vectors
total bitwiseXor : (n : Nat) -> BitVector n -> BitVector n -> BitVector n
bitwiseXor Z [] [] = []
bitwiseXor (S k) (Cons x xs) (Cons y ys) = Cons (xor x y) (bitwiseXor k xs ys)

otpEncrypt : (n: Nat) -> (message : BitVector n) -> (key : BitVector n) -> BitVector n
otpEncrypt n message key = bitwiseXor n message key

otpDecrypt : (n: Nat) -> (cipherText : BitVector n) -> (key : BitVector n) -> BitVector n
otpDecrypt n cipherText key = bitwiseXor n cipherText key

total xorCancel : (x : Bit) -> (y : Bit) -> xor (xor x y) y = x
xorCancel ZeroBit ZeroBit = Refl
xorCancel ZeroBit OneBit = Refl
xorCancel OneBit ZeroBit = Refl
xorCancel OneBit OneBit = Refl

total otpCorrect : (n : Nat) -> (m : BitVector n) -> (k : BitVector n) -> otpDecrypt n (otpEncrypt n m k) k = m
otpCorrect Z [] [] = Refl
otpCorrect (S j) (Cons x xs) (Cons y ys) = let xor_eq = xorCancel x y  in
  rewrite xor_eq in
    let tail_eq = otpCorrect j xs ys in
      rewrite tail_eq in
        Refl
