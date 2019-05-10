/*
 * Copyright (c) 2001, 2009, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package sun.nio.ch;

import java.io.IOException;
import java.nio.channels.*;

public class FileLockImpl
    extends FileLock
{
    private volatile boolean valid = true;

    FileLockImpl(FileChannel channel, long position, long size, boolean shared)
    {
        super(channel, position, size, shared);
    }

    FileLockImpl(AsynchronousFileChannel channel, long position, long size, boolean shared)
    {
        super(channel, position, size, shared);
    }

    public boolean isValid() {
        return valid;
    }

    void invalidate() {
        assert Thread.holdsLock(this);
        valid = false;
    }

    public synchronized void release() throws IOException {
        Channel ch = acquiredBy();
        if (!ch.isOpen())
            throw new ClosedChannelException();
        if (valid) {
            if (ch instanceof FileChannelImpl)
                ((FileChannelImpl)ch).release(this);
            else if (ch instanceof AsynchronousFileChannelImpl)
                ((AsynchronousFileChannelImpl)ch).release(this);
            else throw new AssertionError();
            valid = false;
        }
    }
}
