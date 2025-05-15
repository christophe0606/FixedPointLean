/-
Copyright (c) 2025 Christophe Favergeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christophe Favergeon

-/

import FixedPoint


open BitVec
open FixedPoint

/-! ## Temporary interactive examples for testing

-/

#eval  toString (ofBitVec 0x40#9 : Q .isSigned 9 7)
#eval  toString (ofBitVec 0x40#9 : Q .isSigned 9 7).round


def a : sq15 := 0xffff#16
def b : sq15 := 0x2#16
def c : uq15 := 0xffff#16

def prod  := a * b
def mixedAdd : Q .isSigned 17 15 := (b : Q .isSigned 17 15) + (c : Q .isSigned 17 15)
def bigger := a.widen 64
def narrower := bigger.narrow 16

#eval a
#eval b
#eval c
#eval prod
#eval mixedAdd
#eval bigger
#eval narrower


--#eval prod.narrow 31
--#eval mac (ofInt 1:Q .isSigned 17 14) (0x81#8 : sq7) (4#8 : sq7)
