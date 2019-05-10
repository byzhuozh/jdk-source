/*
 * Copyright (c) 1999, Oracle and/or its affiliates. All rights reserved.
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

package sun.net.www.content.image;

import java.net.URL;
import java.net.URLConnection;
import java.net.*;
import java.io.InputStream;
import java.io.IOException;
import sun.awt.image.*;
import java.awt.Image;
import java.awt.Toolkit;

public class png extends ContentHandler {
    public Object getContent(URLConnection urlc) throws java.io.IOException {
        return new URLImageSource(urlc);
    }

    public Object getContent(URLConnection urlc, Class[] classes) throws IOException {
        for (int i = 0; i < classes.length; i++) {
          if (classes[i].isAssignableFrom(URLImageSource.class)) {
                return new URLImageSource(urlc);
          }
          if (classes[i].isAssignableFrom(Image.class)) {
            Toolkit tk = Toolkit.getDefaultToolkit();
            return tk.createImage(new URLImageSource(urlc));
          }
        }
        return null;
    }
}
