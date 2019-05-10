/*
 * Copyright (c) 2012, Oracle and/or its affiliates. All rights reserved.
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

package sun.awt;

/**
 * A GraphicsConfiguration implements the TextureSizeConstraining
 * interface to indicate that it imposes certain limitations on the
 * maximum size of supported textures.
 */
public interface TextureSizeConstraining {

    /**
     * Returns the maximum width of any texture image.
     */
    public int getMaxTextureWidth();

    /**
     * Returns the maximum height of any texture image.
     */
    public int getMaxTextureHeight();

}
