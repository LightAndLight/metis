{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Metis.Log (
  MonadLog (..),
  WithLoggingT,
  withLogging,
  NoLoggingT,
  noLogging,
) where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Reader.Class (ask)
import qualified Control.Monad.State.Strict
import Control.Monad.Trans.Class (lift)
import Data.Text (Text)
import qualified Data.Text.IO as Text.IO
import qualified System.IO

class (Monad m) => MonadLog m where
  trace :: Text -> m ()

instance (MonadLog m) => MonadLog (Control.Monad.State.Strict.StateT s m) where
  trace = lift . trace

newtype WithLoggingT m a = WithLoggingT {value :: ReaderT (Text -> IO ()) m a}
  deriving (Functor, Applicative, Monad)

withLogging :: WithLoggingT m a -> m a
withLogging ma = runReaderT ma.value (liftIO . Text.IO.hPutStrLn System.IO.stderr)

instance (MonadIO m) => MonadLog (WithLoggingT m) where
  trace s = WithLoggingT $ do
    f <- ask
    liftIO $ f s

newtype NoLoggingT m a = NoLoggingT {value :: m a}
  deriving (Functor, Applicative, Monad)

noLogging :: NoLoggingT m a -> m a
noLogging ma = ma.value

instance (Monad m) => MonadLog (NoLoggingT m) where
  trace _ = pure ()