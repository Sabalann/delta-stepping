{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module Utils where

import qualified Data.Vector.Mutable as V
import qualified Data.Vector.Storable.Mutable as M
import GHC.Base
import GHC.Word
import GHC.Float
import GHC.ForeignPtr
import Foreign.Storable

import Data.Atomics

readVectorTicket :: V.IOVector a -> Int -> IO (Ticket a)
readVectorTicket (V.MVector offset size array) idx
  | idx < 0 || idx >= size = error "Index out of bounds"
  | otherwise = readArrayElem array (offset + idx)

casIOVector :: V.IOVector a -> Int -> Ticket a -> a -> IO (Bool, Ticket a)
casIOVector (V.MVector offset size array) idx check repl
  | idx < 0 || idx >= size = error "Index out of bounds"
  | otherwise = casArrayElem array (offset + idx) check repl

atomicModifyIOVector :: V.IOVector a -> Int -> (a -> (a, b)) -> IO b
atomicModifyIOVector vector idx f = do
  ticket <- readVectorTicket vector idx
  go ticket
  where
    go ticket = do
      let (new, b) = f $ peekTicket ticket
      (success, newTicket) <- casIOVector vector idx ticket new
      if success then
        return b
      else
        go newTicket

casIOVectorFloat :: M.IOVector Float -> Int -> Float -> Float -> IO (Bool, Float)
casIOVectorFloat (M.MVector _ (ForeignPtr addr _)) idx (F# check) (F# repl) = do
  let size = 4

  when (sizeOf (undefined :: Float) /= size) $
    error $ "casIOVectorFloat: Float is not word32-sized (" ++
            show (sizeOf (undefined :: Float)) ++ " /= " ++ show size ++ ")"

  let checkword = stgFloatToWord32 check
      replword = stgFloatToWord32 repl
      !(I# byteoff) = idx * size
  IO $ \s -> case atomicCasWord32Addr# (plusAddr# addr byteoff) checkword replword s of
               (# s', oldword #) ->
                 (# s', (W32# oldword == W32# checkword
                        ,F# (stgWord32ToFloat oldword)) #)

atomicModifyIOVectorFloat :: M.IOVector Float -> Int -> (Float -> (Float, b)) -> IO b
atomicModifyIOVectorFloat vector idx f = do
  value <- M.read vector idx
  go value
  where
    go value = do
      let (new, b) = f value
      (success, original) <- casIOVectorFloat vector idx value new
      if success then
        return b
      else
        go original
      