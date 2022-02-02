module Trace where
  
import qualified Debug.Trace as Debug

----------------------------------------------------------------------------------------
-- Simple helpers for debugging

debug = False

trace :: String -> a -> a
trace s a = if debug then Debug.trace s a else a

traceM :: Applicative f => String -> f ()
traceM s = if debug then Debug.traceM s else pure ()

----------------------------------------------------------------------------------------
