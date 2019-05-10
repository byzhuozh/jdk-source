/*
 * Copyright (c) 2001, 2003, Oracle and/or its affiliates. All rights reserved.
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

/*-
 *      HTTP stream opener
 */

package sun.net.www.protocol.https;

import java.io.IOException;
import java.net.URL;
import java.net.Proxy;

/** open an http input stream given a URL */
public class Handler extends sun.net.www.protocol.http.Handler {
    protected String proxy;
    protected int proxyPort;

    protected int getDefaultPort() {
        return 443;
    }

    public Handler () {
        proxy = null;
        proxyPort = -1;
    }

    public Handler (String proxy, int port) {
        this.proxy = proxy;
        this.proxyPort = port;
    }

    protected java.net.URLConnection openConnection(URL u)
    throws IOException {
        return openConnection(u, (Proxy)null);
    }

    protected java.net.URLConnection openConnection(URL u, Proxy p)
        throws IOException {
        return new HttpsURLConnectionImpl(u, p, this);
    }
}
