module Debug where

import qualified Debug.Trace as D

----------------------------------------------------------------------------------------
-- Debug Helpers

debug = False

trace :: String -> a -> a
trace s a = if debug then D.trace s a else a

traceM :: Applicative f => String -> f ()
traceM s = if debug then D.traceM s else pure ()

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

