/*
 * Copyright (c) 1996, Oracle and/or its affiliates. All rights reserved.
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

package sun.applet;

import java.awt.Toolkit;
import java.awt.Image;
import sun.awt.image.URLImageSource;
import java.net.URL;

class AppletImageRef extends sun.misc.Ref {
    URL url;

    /**
     * Create the Ref
     */
    AppletImageRef(URL url) {
        this.url = url;
    }

    public void flush() {
        super.flush();
    }

    /**
     * Reconsitute the image.  Only called when the ref has been flushed.
     */
    public Object reconstitute() {
        Image img = Toolkit.getDefaultToolkit().createImage(new URLImageSource(url));
        return img;
    }
}
